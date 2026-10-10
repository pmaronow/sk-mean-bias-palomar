module
public import QuantitativeFollowup.AnisotropicRecordedObservationFloorAdapter
public import QuantitativeFollowup.AnisotropicRecordedProfileLawConvergence
public import FRSB.GridMeasureIdentification
public import FRSB.ParisiGridTopology
public import QuantitativeFollowup.ParisiFreeGrid

@[expose] public section

/-! Honest complete-law finite approximation on exact observation times.
The fixed law includes every physical energy record and terminal mark. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem continuous_anisotropicObservationEnergy (D : AnisotropicSpinModel n) :
    Continuous (anisotropicObservationEnergy D) := by
  unfold anisotropicObservationEnergy anisotropicObservationParameter
  exact (anisotropicEnergyMap D).continuous.comp
    (((anisotropicDisorderInjection n).continuous.comp continuous_fst).add
      ((anisotropicUnitInput D).continuous.comp continuous_snd))

def anisotropicRecordedEnergyProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    ProbabilityMeasure (FiniteStateField (Configuration n)×Records (FiniteStateField (Configuration n)) (Configuration n) T) :=
  (anisotropicRecordedProfileProbability D μ a q T).map
    (Prod.map (anisotropicObservationEnergy D) (observationTreeMap (anisotropicObservationEnergy D) T))

theorem anisotropicRecordedEnergyProbability_measure (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    (anisotropicRecordedEnergyProbability D μ a q T:Measure _)=
      (anisotropicRecordedProfileTreeLaw D μ a q T).map
        (Prod.map (anisotropicObservationEnergy D) (observationTreeMap (anisotropicObservationEnergy D) T)) := rfl

theorem tendsto_anisotropicRecordedEnergyProbability {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n) {μ : L→Paper.ParisiMeasure}
    {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ) (q : ℕ→Paper.Overlap)
    {J : ℕ} (T : FiniteTerminalGenealogy J) (hq : Antitone q) :
    Tendsto (fun j=>anisotropicRecordedEnergyProbability D (μ j) a q T) l
      (𝓝 (anisotropicRecordedEnergyProbability D ν a q T)) := by
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_anisotropicRecordedProfileProbability D hμ a q T (fun j _=>hq (Nat.le_succ j)))
  exact (continuous_anisotropicObservationEnergy D).prodMap
    (continuous_observationTreeMap _ (continuous_anisotropicObservationEnergy D) T)

theorem tendsto_anisotropicRecordedEnergyProbability_grid (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) {J : ℕ}
    (T : FiniteTerminalGenealogy J) (hq : Antitone q) :
    Tendsto (fun N=>anisotropicRecordedEnergyProbability D (Paper.parisiGridMeasure μ N) a q T) atTop
      (𝓝 (anisotropicRecordedEnergyProbability D μ a q T)) :=
  tendsto_anisotropicRecordedEnergyProbability D (FRSB.tendsto_parisiGridMeasure μ) a q T hq

/-- Every actual grid approximation has an exact finite recorded realization
with the original prescribed observation times and the true profile floor. -/
theorem anisotropicRecordedEnergyProbability_grid_finite_realization (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a≤Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (J : ℕ) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J) (N : ℕ) :
    ∃(K : ℕ)(r : RSBScheme K)(d : ℕ→ℕ)(hdepth : observationRefinementDepth d J=K+2),
      Paper.parisiSchemeMeasure r=Paper.parisiGridMeasure μ N ∧ r.q 1=0 ∧ a≤r.m 1 ∧
      (anisotropicFiniteRecordedTreeLaw D r a
        (observationTreeDepthCast hdepth (observationRefineTree d T))).map
          (Prod.map id (observationRefinementDepthProject (S:=Configuration n) d T hdepth))=
        (anisotropicRecordedEnergyProbability D (Paper.parisiGridMeasure μ N) a q T:Measure _) := by
  have hs : (Paper.parisiGridRSBScheme μ N).q 1=0:=Paper.parisiGridSchemeOverlap_one N
  have hm:=FRSB.parisiSchemeMeasure_grid_eq μ N
  have hfloor : a≤Paper.parisiCDF (Paper.parisiSchemeMeasure (Paper.parisiGridRSBScheme μ N)) 0 := by
    rw [hm]
    rw [←zeroMass_eq_parisiCDF_zero,parisiGridMeasure_root_mass,zeroMass_eq_parisiCDF_zero]
    exact ha
  obtain ⟨K,r,d,hdepth,hr,hrzero,har,hlaw⟩:=
    exists_anisotropic_finite_recorded_floor_observation_adapter D (Paper.parisiGridRSBScheme μ N)
      hs a hfloor q hq J hJ hzero htop T
  refine ⟨K,r,d,hdepth,hr.trans hm,hrzero,har,?_⟩
  rw [hm] at hlaw
  exact hlaw

end QuantitativeFollowup
