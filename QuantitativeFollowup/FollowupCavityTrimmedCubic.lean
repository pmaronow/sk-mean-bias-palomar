module
public import QuantitativeFollowup.FollowupCavityFinitePairCubic
public import QuantitativeFollowup.FollowupCavityDegeneratePairCubic

@[expose] public section

/-! Literal terminal-leaf defects under the trimmed finite physical law.
Their cubic domination is derived from the complete native recorded law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityRecordedLeafPairDefect (s : RSBScheme k) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (i l : ObservationLeaf T) {E : Type} (z : Records E (Configuration (n+1)) T) : ℝ :=
  cavitySpinOverlapDefect n (cavityProfileLevel s (observationCommonLevel T i l))
    (observationLeafSpin T i z) (observationLeafSpin T l z)

theorem measurable_cavityRecordedLeafPairDefect (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i l : ObservationLeaf T) {E : Type} [MeasurableSpace E] :
    Measurable (cavityRecordedLeafPairDefect (n:=n) s T i l (E:=E)) := by
  let b : (Configuration (n+1) × Configuration (n+1)) → ℝ :=fun z=>
    cavitySpinOverlapDefect n (cavityProfileLevel s (observationCommonLevel T i l)) z.1 z.2
  let p : Records E (Configuration (n+1)) T → (Configuration (n+1) × Configuration (n+1)) :=
    fun z=>(observationLeafSpin T i z,observationLeafSpin T l z)
  have hp : Measurable p:=
    (measurable_observationLeafSpin (E:=E) (S:=Configuration (n+1)) T i).prodMk
      (measurable_observationLeafSpin (E:=E) (S:=Configuration (n+1)) T l)
  change Measurable (fun z => b (p z))
  exact (measurable_of_finite b).comp hp

def cavityTrimmedRecordedTripleDefectMoment (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (i l : Fin 3→ObservationLeaf (trimRoot T)) : ℝ :=
  ∫z,|cavityRecordedLeafPairDefect s (trimRoot T) (i 0) (l 0) z.2*
    cavityRecordedLeafPairDefect s (trimRoot T) (i 1) (l 1) z.2*
    cavityRecordedLeafPairDefect s (trimRoot T) (i 2) (l 2) z.2|
      ∂anisotropicTrimmedRecordedTreeLaw D s a T

theorem cavityTrimmedRecordedTripleDefectMoment_le_branch (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 3→ObservationLeaf (trimRoot T)) :
    cavityTrimmedRecordedTripleDefectMoment D s a T i l≤
      finiteCascadeUnweightedBranchSum
        (fun j=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s j)) (trimRoot T) := by
  letI : MeasurableSpace (Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T)) :=
    recordMeasurableSpace _ _ (trimRoot T)
  let F : FiniteStateField (Configuration (n+1))×Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T) → ℝ := fun z =>
    |cavityRecordedLeafPairDefect s (trimRoot T) (i 0) (l 0) z.2*
      cavityRecordedLeafPairDefect s (trimRoot T) (i 1) (l 1) z.2*
      cavityRecordedLeafPairDefect s (trimRoot T) (i 2) (l 2) z.2|
  have hsnd := @measurable_snd (FiniteStateField (Configuration (n+1)))
    (Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T))
    inferInstance (recordMeasurableSpace _ _ (trimRoot T))
  have hpair (r : Fin 3) : Measurable (fun z : FiniteStateField (Configuration (n+1)) ×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T) =>
      cavityRecordedLeafPairDefect (n:=n) s (trimRoot T) (i r) (l r) z.2) := by
    exact (measurable_cavityRecordedLeafPairDefect (n:=n) (E:=FiniteStateField (Configuration (n+1))) s (trimRoot T) (i r) (l r)).comp hsnd
  have hF : Measurable F := ((hpair 0).mul (hpair 1) |>.mul (hpair 2)).abs
  let φ : AnisotropicObservationState (n+1)×Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) (.advance (trimRoot T))→
      FiniteStateField (Configuration (n+1))×Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T):=
    fun z=>(anisotropicObservationEnergy D z.1,observationTreeMap (anisotropicObservationEnergy D) (trimRoot T) z.2.2)
  have hφ : Measurable φ:=((measurable_anisotropicObservationEnergy D).comp measurable_fst).prodMk
    ((measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) (trimRoot T)).comp
      (measurable_snd.comp measurable_snd))
  have hm : (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a
      (cavityProfileLevel s) (.advance (trimRoot T))).map φ=anisotropicTrimmedRecordedTreeLaw D s a T := by
    exact anisotropicRecordedProfileTreeLaw_scheme_trimmed_energy D s a hq (.advance (trimRoot T))
  have hi:=integral_map (μ:=anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a
    (cavityProfileLevel s) (.advance (trimRoot T))) hφ.aemeasurable hF.aestronglyMeasurable
  rw [hm] at hi
  have he : (fun z=>F (φ z))=(fun z=>|cavitySpinOverlapDefect n
      (cavityProfileLevel s (observationCommonLevel (.advance (trimRoot T)) (i 0) (l 0)))
      (observationLeafSpin (.advance (trimRoot T)) (i 0) z.2) (observationLeafSpin (.advance (trimRoot T)) (l 0) z.2)*
      cavitySpinOverlapDefect n (cavityProfileLevel s (observationCommonLevel (.advance (trimRoot T)) (i 1) (l 1)))
      (observationLeafSpin (.advance (trimRoot T)) (i 1) z.2) (observationLeafSpin (.advance (trimRoot T)) (l 1) z.2)*
      cavitySpinOverlapDefect n (cavityProfileLevel s (observationCommonLevel (.advance (trimRoot T)) (i 2) (l 2)))
      (observationLeafSpin (.advance (trimRoot T)) (i 2) z.2) (observationLeafSpin (.advance (trimRoot T)) (l 2) z.2)|) := by
    funext z
    dsimp [F,φ,cavityRecordedLeafPairDefect,observationCommonLevel,observationLeafSpin]
    simp only [observationLeafSpin_treeMap]
  rw [he] at hi
  change cavityTrimmedRecordedTripleDefectMoment D s a T i l= _ at hi
  rw [hi]
  obtain ⟨hzero,hroot,hmono⟩:=cavityProfileLevel_clock s
  exact cavityRecorded_threeDefects_le_branch_cubic_all_pairs hn D (Paper.parisiSchemeMeasure s) a
    (cavityProfileLevel s) hzero (.advance (trimRoot T)) hroot hmono i l

end QuantitativeFollowup
