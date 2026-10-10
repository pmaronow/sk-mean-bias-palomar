module
public import QuantitativeFollowup.AnisotropicRecordedObservationRefinement
public import QuantitativeFollowup.AnisotropicRecordedObservationApproximation

@[expose] public section

/-! Insert an actual observation at a variable point of one physical edge.
The exact normalized native law retains every original field and terminal
spin under the explicit projection; the inserted state is never a cell
representative of a finite profile. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
variable {n J : ℕ}

def nativeStreamingEdgeSubdivision (j : ℕ) (k : ℕ) : ℕ := if k=j then 1 else 0

def nativeStreamingEdgeSchedule (q : ℕ→Paper.Overlap) (j : ℕ)
    (r : Paper.Overlap) (k : ℕ) : Paper.Overlap :=
  if k≤j then q k else if k=j+1 then r else q (k-1)

theorem nativeStreamingEdgeSubdivision_depth (j k : ℕ) :
    observationRefinementDepth (nativeStreamingEdgeSubdivision j) k=
      if k≤j then k else k+1 := by
  induction k with
  | zero => simp [observationRefinementDepth]
  | succ k ih =>
      rw [observationRefinementDepth,ih]
      unfold nativeStreamingEdgeSubdivision
      split_ifs <;> omega

theorem nativeStreamingEdgeSchedule_refinement (q : ℕ→Paper.Overlap)
    (j : ℕ) (r : Paper.Overlap) (k : ℕ) :
    nativeStreamingEdgeSchedule q j r
      (observationRefinementDepth (nativeStreamingEdgeSubdivision j) k)=q k := by
  rw [nativeStreamingEdgeSubdivision_depth]
  unfold nativeStreamingEdgeSchedule
  split_ifs <;> simp_all <;> omega

theorem nativeStreamingEdgeSchedule_inserted (q : ℕ→Paper.Overlap)
    (j : ℕ) (r : Paper.Overlap) :
    nativeStreamingEdgeSchedule q j r (j+1)=r := by
  simp [nativeStreamingEdgeSchedule]

theorem nativeStreamingEdgeSchedule_antitone (q : ℕ→Paper.Overlap)
    (hq : Antitone q) (j : ℕ) (r : Paper.Overlap)
    (hr : q (j+1)≤r ∧ r≤q j) :
    Antitone (nativeStreamingEdgeSchedule q j r) := by
  apply antitone_nat_of_succ_le
  intro k
  by_cases hlt:k<j
  · have hsucc:k+1≤j:=by omega
    simp only [nativeStreamingEdgeSchedule,if_pos (by omega : k≤j),if_pos hsucc]
    exact hq (Nat.le_succ k)
  · by_cases he:k=j
    · subst k
      simpa [nativeStreamingEdgeSchedule,show ¬(j+1≤j) by omega] using hr.2
    · by_cases he':k=j+1
      · subst k
        simpa [nativeStreamingEdgeSchedule,
          show ¬(j+1+1≤j) by omega,show ¬(j+1+1=j+1) by omega,
          show ¬(j+1≤j) by omega] using hr.1
      · have hk:j+1<k:=by omega
        simp only [nativeStreamingEdgeSchedule,
          if_neg (show ¬(k≤j) by omega),if_neg he',
          if_neg (show ¬(k+1≤j) by omega),if_neg (show ¬(k+1=j+1) by omega),
          Nat.add_sub_cancel]
        exact hq (by omega : k-1≤k)

theorem anisotropicRecordedProfileTreeLaw_native_edge_insertion
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (j : ℕ) (r : Paper.Overlap)
    (hr : q (j+1)≤r ∧ r≤q j) (T : FiniteTerminalGenealogy J) :
    (anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingEdgeSchedule q j r)
      (observationRefineTree (nativeStreamingEdgeSubdivision j) T)).map
        (Prod.map id (observationRefinementProject (nativeStreamingEdgeSubdivision j) T))=
      anisotropicRecordedProfileTreeLaw D μ a q T := by
  exact anisotropicRecordedProfileTreeLaw_refinement D μ a q _ _
    (nativeStreamingEdgeSchedule_antitone q hq j r hr)
    (nativeStreamingEdgeSchedule_refinement q j r) T

theorem anisotropicRecordedEnergyProbability_native_edge_insertion
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (j : ℕ) (r : Paper.Overlap)
    (hr : q (j+1)≤r ∧ r≤q j) (T : FiniteTerminalGenealogy J) :
    (anisotropicRecordedEnergyProbability D μ a (nativeStreamingEdgeSchedule q j r)
      (observationRefineTree (nativeStreamingEdgeSubdivision j) T):
        Measure (FiniteStateField (Configuration n)×
          Records (FiniteStateField (Configuration n)) (Configuration n)
            (observationRefineTree (nativeStreamingEdgeSubdivision j) T))).map
        (Prod.map id (observationRefinementProject (nativeStreamingEdgeSubdivision j) T))=
      (anisotropicRecordedEnergyProbability D μ a q T:
        Measure (FiniteStateField (Configuration n)×
          Records (FiniteStateField (Configuration n)) (Configuration n) T)) := by
  rw [anisotropicRecordedEnergyProbability_measure,Measure.map_map
    (measurable_id.prodMap (measurable_observationRefinementProject _ _))
    ((measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) _))]
  rw [anisotropicRecordedEnergyProbability_measure,
    ←anisotropicRecordedProfileTreeLaw_native_edge_insertion D μ a q hq j r hr T,
    Measure.map_map]
  · congr 1
    funext z
    apply Prod.ext
    · rfl
    · exact (congrFun (observationRefinementProject_map (anisotropicObservationEnergy D)
        (nativeStreamingEdgeSubdivision j) T) z.2).symm
  · exact (measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) _)
  · exact measurable_id.prodMap (measurable_observationRefinementProject _ _)

end QuantitativeFollowup
