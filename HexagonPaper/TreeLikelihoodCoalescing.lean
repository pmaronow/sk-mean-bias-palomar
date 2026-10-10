module
public import HexagonPaper.TreeLikelihoodNative
public import HexagonPaper.TreePathWeightIntegrals
public import HexagonPaper.EdgeLikelihoodPathKernelSourceLog

@[expose] public section

/-! The literal positive Stieltjes tree action for arbitrary profiles.
A closed-upper-endpoint edge carries its actual profile atoms; fork
charges coalesce the endpoint factors. Every potential below is the
constructed native tail potential evaluated on the actual path record. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ENNReal
namespace HexagonPaper
open FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

def treeNativeSourceLog (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j):
    AnisotropicObservationState n→Records (NativeTreePath n) (Configuration n) T→ℝ:=
  treePathLogDensity (treeNativeSpinLog D μ)
    (fun j=>edgePathSourceLog D μ (q (j+1)) (q j))
    (fun j=>edgePathEndpoint D (q j)) T

theorem treeNativePathKernel_source_exp_density (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) (hq : ∀j,q (j+1)≤q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j):
    treeNativePathKernel D μ q T=(treeReferencePathKernel D q T).withDensity
      (fun x Z=>ENNReal.ofReal (Real.exp (treeNativeSourceLog D μ q T x Z))) := by
  unfold treeNativePathKernel treeReferencePathKernel treeNativeSourceLog
  exact treePathRecordKernel_exp_density _ _ _ _ _ _ _ _
    (measurable_treeNativeSpinLog D μ)
    (fun j=>measurable_edgePathSourceLog D μ (q (j+1)) (q j))
    (treeNativeSpinKernel_exp_density D μ)
    (fun j=>edgePhysicalPathKernel_source_exp_density D μ _ _ (hq j)) T

@[reducible] def treeNativeInteriorPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap):
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→AnisotropicObservationState n→
      Records (NativeTreePath n) (Configuration n) T→treePathWeightPoint T→ℝ
  | _,.leaf=>fun _ _ _=>0
  | _,@FiniteTerminalGenealogy.advance j T=>fun x Z=>Sum.elim
      (fun r=>anisotropicMeasureTailPotential D μ r (Z.1 r))
      (treeNativeInteriorPotential D μ q T (edgePathEndpoint D (q j) Z.1) Z.2)
  | j,.fork T U=>fun x Z=>Sum.elim
      (fun _:Unit=>anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D x))
      (Sum.elim (treeNativeInteriorPotential D μ q T x Z.1)
        (treeNativeInteriorPotential D μ q U x Z.2))

@[reducible] def treeNativeTerminalEnergy (D : AnisotropicSpinModel n) (q : ℕ→Paper.Overlap):
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→AnisotropicObservationState n→
      Records (NativeTreePath n) (Configuration n) T→ℝ
  | _,.leaf=>fun x σ=>anisotropicTerminalLinear D σ (anisotropicObservationParameter D x)
  | _,@FiniteTerminalGenealogy.advance j T=>fun _ Z=>
      treeNativeTerminalEnergy D q T (edgePathEndpoint D (q j) Z.1) Z.2
  | _,.fork T U=>fun x Z=>treeNativeTerminalEnergy D q T x Z.1+
      treeNativeTerminalEnergy D q U x Z.2

theorem measurable_treeNativeInteriorPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T):
    Measurable (treeNativeInteriorPotential D μ q T x Z):=by
  induction T generalizing x with
  | leaf=>exact measurable_const
  | @advance j T ih=>
    exact (edgeNativePathPotential D μ Z.1).continuous.measurable.sumElim
      (ih (edgePathEndpoint D (q j) Z.1) Z.2)
  | fork T U ihT ihU=>
    exact measurable_const.sumElim ((ihT x Z.1).sumElim (ihU x Z.2))

theorem treeNativeSourceLog_coalesced (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (h0 : q 0=1)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T):
    Integrable (treeNativeInteriorPotential D μ q T x Z) (treePathInteriorWeight μ q T) ∧
    treeNativeSourceLog D μ q T x Z=treeNativeTerminalEnergy D q T x Z-
      Paper.parisiCDF μ (q j)*anisotropicMeasureTailPotential D μ (q j)
        (anisotropicObservationParameter D x)-
      ∫v,treeNativeInteriorPotential D μ q T x Z v ∂treePathInteriorWeight μ q T := by
  induction T generalizing x with
  | leaf=>
    refine ⟨integrable_const _,?_⟩
    simp only [treeNativeSourceLog,treePathLogDensity,treeNativeSpinLog,
      treeNativeTerminalEnergy,treeNativeInteriorPotential,treePathInteriorWeight,h0,
      integral_zero_measure,sub_zero]
    have hc:Paper.parisiCDF μ ((1:Paper.Overlap):ℝ)=1:=by
      change Paper.parisiCDF μ (1:ℝ)=1
      exact Paper.parisiCDF_eq_one_of_one_le μ le_rfl
    rw [hc,one_mul]
  | @advance j T ih=>
    obtain ⟨hi,he⟩:=ih (edgePathEndpoint D (q j) Z.1) Z.2
    have hF:=continuousMap_integrable_probability (edgeNativePathPotential D μ Z.1) μ
    have hsum:=treePathInteriorWeight_advance_integral μ q T
      (fun r=>anisotropicMeasureTailPotential D μ r (Z.1 r))
      (treeNativeInteriorPotential D μ q T (edgePathEndpoint D (q j) Z.1) Z.2)
      (edgeNativePathPotential D μ Z.1).continuous.measurable
      (measurable_treeNativeInteriorPotential D μ q T _ _) hF.restrict hi
    refine ⟨hsum.1,?_⟩
    change edgePathSourceLog D μ (q (j+1)) (q j) x Z.1+
      treeNativeSourceLog D μ q T (edgePathEndpoint D (q j) Z.1) Z.2=_
    rw [he,hsum.2]
    rw [anisotropicObservationParameter_edgePathEndpoint]
    unfold edgePathSourceLog
    change _=treeNativeTerminalEnergy D q T (edgePathEndpoint D (q j) Z.1) Z.2-_-_
    ring
  | @fork j T U ihT ihU=>
    obtain ⟨hiT,heT⟩:=ihT x Z.1
    obtain ⟨hiU,heU⟩:=ihU x Z.2
    have hsum:=treePathInteriorWeight_fork_integral μ q T U
      (anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D x))
      (treeNativeInteriorPotential D μ q T x Z.1) (treeNativeInteriorPotential D μ q U x Z.2)
      (measurable_treeNativeInteriorPotential D μ q T x Z.1)
      (measurable_treeNativeInteriorPotential D μ q U x Z.2) hiT hiU
    refine ⟨hsum.1,?_⟩
    change treeNativeSourceLog D μ q T x Z.1+treeNativeSourceLog D μ q U x Z.2=_
    rw [heT,heU,hsum.2]
    change _=treeNativeTerminalEnergy D q T x Z.1+treeNativeTerminalEnergy D q U x Z.2-_-_
    ring

def treeNativeFullPotential (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T):
    Unit⊕treePathWeightPoint T→ℝ:=
  Sum.elim (fun _:Unit=>anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D x))
    (treeNativeInteriorPotential D μ q T x Z)

theorem treeNativeSourceLog_full_weight (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (h0 : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T):
    Integrable (treeNativeFullPotential D μ q T x Z) (treePathWeight μ a q T) ∧
    a*anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D x)+
      treeNativeSourceLog D μ q T x Z=treeNativeTerminalEnergy D q T x Z-
      ∫v,treeNativeFullPotential D μ q T x Z v ∂treePathWeight μ a q T:=by
  obtain ⟨hi,he⟩:=treeNativeSourceLog_coalesced D μ q h0 T x Z
  have hsum:=treePathWeight_root_integral μ a hμ q T
    (anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D x))
    (treeNativeInteriorPotential D μ q T x Z)
    (measurable_treeNativeInteriorPotential D μ q T x Z) hi
  refine ⟨hsum.1,?_⟩
  rw [he]
  unfold treeNativeFullPotential
  rw [hsum.2]
  ring

end HexagonPaper
