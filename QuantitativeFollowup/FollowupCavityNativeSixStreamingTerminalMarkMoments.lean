module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeMarkLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingApproximation
public import FourPapersCommon.FiniteObservationTerminalProjection

@[expose] public section

/-! Actual fresh-spin tree moments are continuous under weak profiles and
moving ancestral observations. A bounded test is constructed internally
from the finite terminal-spin space, retaining the complete old record. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J : ℕ}
variable {A:Type} [Fintype A] [MeasurableSpace A] [TopologicalSpace A]
    [DiscreteTopology A] [BorelSpace A] [SecondCountableTopology A]
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def nativeStreamingTerminalMarkMoment {T:FiniteTerminalGenealogy J} (P : ProbabilityMeasure
    ((AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T)×A))
    (G : TerminalSpins (Configuration n) T×A→ℝ) : ℝ :=
  ∫z,G (finiteCascadeRecordTerminalSpins T z.1.2,z.2) ∂(P:Measure ((AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T)×A))

def nativeStreamingTerminalMarkBound (T:FiniteTerminalGenealogy J)
    (G:TerminalSpins (Configuration n) T×A→ℝ) : ℝ :=
  ∑σ:TerminalSpins (Configuration n) T×A,‖G σ‖

theorem nativeStreamingTerminalMarkBound_nonneg (T:FiniteTerminalGenealogy J)
    (G:TerminalSpins (Configuration n) T×A→ℝ) :
    0≤nativeStreamingTerminalMarkBound T G :=
  Finset.sum_nonneg (fun _ _=>norm_nonneg _)

theorem nativeStreamingTerminalMarkMoment_abs_le {T:FiniteTerminalGenealogy J}
    (P:ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×A))
    (G:TerminalSpins (Configuration n) T×A→ℝ) :
    |nativeStreamingTerminalMarkMoment P G|≤nativeStreamingTerminalMarkBound T G := by
  classical
  have hb (σ:TerminalSpins (Configuration n) T×A):
      ‖G σ‖≤nativeStreamingTerminalMarkBound T G:=
    Finset.single_le_sum (fun σ _=>norm_nonneg (G σ)) (Finset.mem_univ σ)
  simpa only [nativeStreamingTerminalMarkMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=(P:Measure ((AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T)×A))) (.of_forall fun z=>hb _)

theorem tendsto_nativeStreamingTerminalMarkMoment
    {L:Type*} {l:Filter L} {T:FiniteTerminalGenealogy J}
    {Pj:L→ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×A)}
    {P:ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×A)}
    (hP:Tendsto Pj l (𝓝 P)) (G:TerminalSpins (Configuration n) T×A→ℝ) :
    Tendsto (fun N=>nativeStreamingTerminalMarkMoment (Pj N) G) l
      (𝓝 (nativeStreamingTerminalMarkMoment P G)) := by
  classical
  let C:ℝ:=∑σ:TerminalSpins (Configuration n) T×A,‖G σ‖
  have hb (σ:TerminalSpins (Configuration n) T×A):‖G σ‖≤C:=
    Finset.single_le_sum (fun σ _=>norm_nonneg (G σ)) (Finset.mem_univ σ)
  let f:((AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T)×
      A)→ᵇℝ:=BoundedContinuousFunction.mkOfBound
    ⟨fun z=>G (finiteCascadeRecordTerminalSpins T z.1.2,z.2),
      (continuous_of_discreteTopology (f:=G)).comp
        (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk continuous_snd)⟩
    (2*C) (fun z w=>(dist_le_norm_add_norm _ _).trans
      ((add_le_add (hb _) (hb _)).trans_eq (by ring)))
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hP f

theorem tendsto_nativeStreamingEdgeTerminalMarkMoment
    {L:Type*} {l:Filter L} [l.IsCountablyGenerated] (D:AnisotropicSpinModel n)
    {μj:L→Paper.ParisiMeasure} {μ:Paper.ParisiMeasure} (hμ:Tendsto μj l (𝓝 μ))
    (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q) (T:FiniteTerminalGenealogy J)
    (e:NativeStreamingEdge T) {rj:L→Paper.Overlap} {r:Paper.Overlap}
    (hr:Tendsto rj l (𝓝 r))
    (hrj:∀N,q (e.depth+1)≤rj N ∧ rj N≤q e.depth)
    (hrr:q (e.depth+1)≤r ∧ r≤q e.depth)
    (G:TerminalSpins (Configuration n) T×Configuration n→ℝ) :
    Tendsto (fun N=>nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgeSingleMarkProbability D (μj N) a q T e (rj N)) G) l
      (𝓝 (nativeStreamingTerminalMarkMoment
        (nativeStreamingEdgeSingleMarkProbability D μ a q T e r) G)) :=
  tendsto_nativeStreamingTerminalMarkMoment
    (tendsto_nativeStreamingEdgeSingleMarkProbability D hμ a q hq T e hr hrj hrr) G

theorem continuous_nativeStreamingEdgeTerminalMarkMoment (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q)
    (T:FiniteTerminalGenealogy J) (e:NativeStreamingEdge T)
    (G:TerminalSpins (Configuration n) T×Configuration n→ℝ) :
    Continuous (fun r:Icc (q (e.depth+1)) (q e.depth)=>
      nativeStreamingTerminalMarkMoment (nativeStreamingEdgeSingleMarkProbability D μ a q T e r) G) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  exact tendsto_nativeStreamingEdgeTerminalMarkMoment D tendsto_const_nhds a q hq T e
    (continuous_subtype_val.tendsto r) (fun x=>x.2) r.2 G

theorem integrableOn_nativeStreamingEdgeTerminalMarkMoment (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q)
    (T:FiniteTerminalGenealogy J) (e:NativeStreamingEdge T)
    (G:TerminalSpins (Configuration n) T×Configuration n→ℝ) :
    IntegrableOn (fun r=>nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgeSingleMarkProbability D μ a q T e r) G)
      (Ioo (q (e.depth+1)) (q e.depth)) (parisiFreeMeasure μ a) := by
  have hc:ContinuousOn (fun r=>nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgeSingleMarkProbability D μ a q T e r) G)
      (Icc (q (e.depth+1)) (q e.depth)) :=
    continuousOn_iff_continuous_restrict.mpr
      (continuous_nativeStreamingEdgeTerminalMarkMoment D μ a q hq T e G)
  exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

end QuantitativeFollowup
