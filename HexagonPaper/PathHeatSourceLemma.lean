module
public import HexagonPaper.PathHeatSectionwiseNativeWienerEndpoints
public import HexagonPaper.PathHeatSectionwiseNativeWienerPrinted
public import HexagonPaper.PathHeatFiniteTreeSource
public import HexagonPaper.PathHeatNativeFieldCovariance

@[expose] public section

/-! The normalized Gaussian path heat lemma on the genuine reference law.
The source derivative measures retain their original index and atoms.
Auxiliary signed jets need only fixed-auxiliary TV continuity. Actual
Gaussian observations, finite Price differentiation, raw auxiliary/count
integration, Bernstein limits and common Fernique domination are proved
inside the imported chain. No density, response, normalizer positivity,
finite derivative or limiting derivative is an input hypothesis. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal ENNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X E K : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L : ℕ} {a b : ℝ}

/-- The dot-kernel in the printed identity is the derivative of the actual
Gaussian field covariance, including ancestor and terminal contributions. -/
theorem pathHeatSource_actual_covariance_derivative
    (hab : a≤b) (ι : C(X,Fin L×I))
    (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (hc : ∀u l,Monotone (c u l)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (z : ℝ) (hdc : ∀l t,HasDerivAt (fun u=>(c (projIcc a b hab u) l t:ℝ))
      (dc (projIcc a b hab z) l t) z) (x y : X) :
    HasDerivAt (fun u=>covariance
      (fun w=>pathHeatNativeClockField ι (c (projIcc a b hab u)) δ W w x)
      (fun w=>pathHeatNativeClockField ι (c (projIcc a b hab u)) δ W w y)
      (pathHeatWienerMeshBase (J:=Fin L)))
      (pathHeatSectionwiseNativeWienerKernel ι dc δ W (projIcc a b hab z) (x,y)) z :=
  hasDerivAt_covariance_pathHeatNativeClockField hab ι c dc hc δ W z hdc x y

/-- The exact right side of (fnd-path-heat), including its centered signed
measure contraction and the finite counting sum in every expectation. -/
def pathHeatSourcePrintedResponse (μ : Measure E)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (dc : Icc a b→Fin L→C(I,ℝ)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (z : Icc a b) : ℝ :=
  pathHeatSectionwiseNativeWienerMean μ d ι c δ W z d.dotphi+
    (pathHeatSectionwiseNativeWienerMean μ d ι c δ W z (fun θ=>d.phi θ*d.dotell θ)-
      pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W z*
        pathHeatSectionwiseNativeWienerMean μ d ι c δ W z d.dotell)+
    (1/2:ℝ)*pathHeatSectionwiseNativeWienerMean μ d ι c δ W z
      (d.centeredContraction (pathHeatSectionwiseNativeWienerKernel ι dc δ W z)
        (pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W z))

/-- The exact right side of (fnd-path-normalizer). -/
def pathHeatSourcePrintedLogNormalizerResponse (μ : Measure E)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (dc : Icc a b→Fin L→C(I,ℝ)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (z : Icc a b) : ℝ :=
  pathHeatSectionwiseNativeWienerMean μ d ι c δ W z d.dotell+
    (1/2:ℝ)*pathHeatSectionwiseNativeWienerMean μ d ι c δ W z
      (d.densityContraction (pathHeatSectionwiseNativeWienerKernel ι dc δ W z))

theorem pathHeatSourcePrintedResponse_eq_response
    (μ : Measure E) [IsGaussian μ] (hab : a≤b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (dc : Icc a b→Fin L→C(I,ℝ)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hdc : ∀l,Continuous (fun z=>dc z l)) (z : Icc a b) :
    pathHeatSourcePrintedResponse μ d ι c dc δ W z=
      pathHeatSectionwiseNativeWienerResponse μ d ι c dc δ W z :=
  (pathHeatSectionwiseNativeWienerResponse_printed μ d ι c dc δ W hab C hs hdc z).symm

theorem pathHeatSourcePrintedLogNormalizerResponse_eq_response
    (μ : Measure E) [IsGaussian μ] (hab : a≤b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (dc : Icc a b→Fin L→C(I,ℝ)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hdc : ∀l,Continuous (fun z=>dc z l)) (z : Icc a b) :
    pathHeatSourcePrintedLogNormalizerResponse μ d ι c dc δ W z=
      pathHeatSectionwiseNativeWienerLogNormalizerResponse μ d ι c dc δ W z :=
  (pathHeatSectionwiseNativeWienerLogNormalizerResponse_printed μ d ι c dc δ W hab C hs hdc z).symm

/-- Source Lemma 2.3, with actual counting normalization, arbitrary fixed
Gaussian auxiliary law, interior C1, and genuine one-sided endpoint formulas.
Only interior clocks are required to be strict; endpoint variances may vanish.
The covariance and its derivative are identified with actual Gaussian field
covariances by `hasDerivAt_covariance_pathHeatNativeClockField`. -/
theorem lem_fnd_path_heat
    (μ : Measure E) [IsGaussian μ] (hab : a<b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab.le d C)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdcc : ∀l,Continuous (fun z=>dc z l))
    (hstrict : ∀z : Icc a b,z.val∈Ioo a b→∀l,StrictMono (c z l))
    (hroot : ∀z l,c z l 0=0)
    (hdc : ∀z∈Ioo a b,∀l t,
      HasDerivAt (fun u=>(c (projIcc a b hab.le u) l t:ℝ))
        (dc (projIcc a b hab.le z) l t) z) :
    let f := fun u=>pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W (projIcc a b hab.le u)
    let r := fun u=>pathHeatSourcePrintedResponse μ d ι c dc δ W (projIcc a b hab.le u)
    let g := fun u=>Real.log (pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W (projIcc a b hab.le u))
    let s := fun u=>pathHeatSourcePrintedLogNormalizerResponse μ d ι c dc δ W (projIcc a b hab.le u)
    (∀z,0<pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W z) ∧
    (∀x∈Ioo a b,HasDerivAt f (r x) x ∧ HasDerivAt g (s x) x) ∧
    ContDiffOn ℝ 1 f (Ioo a b) ∧ ContDiffOn ℝ 1 g (Ioo a b) ∧
    HasDerivWithinAt f (r a) (Ici a) a ∧ HasDerivWithinAt f (r b) (Iic b) b ∧
    HasDerivWithinAt g (s a) (Ici a) a ∧ HasDerivWithinAt g (s b) (Iic b) b := by
  dsimp only
  have he := pathHeatSectionwiseNativeWiener_C1_and_endpoints μ hab d C hs ι c dc δ W
    hc hdcc hstrict hroot hdc
  have hR := pathHeatSourcePrintedResponse_eq_response μ hab.le d C hs ι c dc δ W hdcc
  have hS := pathHeatSourcePrintedLogNormalizerResponse_eq_response μ hab.le d C hs ι c dc δ W hdcc
  refine ⟨?_,?_,he.1,he.2.1,?_,?_,?_,?_⟩
  · intro z
    rw [pathHeatSectionwiseNativeWienerNormalizer_eq_card_flat]
    exact mul_pos (by exact_mod_cast Fintype.card_pos) (pathHeatSectionwiseWiener_positive_normalizer
      μ (pathHeatSectionwiseNativeSourceExtension ι d) c δ W hab.le C
      (pathHeatSectionwiseNativeSourceExtension_analytic hab.le ι d C hs) z)
  · intro x hx
    have h := pathHeatSectionwiseNativeWiener_differentiation μ hab.le d C hs ι c dc δ W
      hc hdcc hstrict hroot hdc x hx
    rw [hR,hS]
    exact h.2
  · rw [hR]
    exact he.2.2.1
  · rw [hR]
    exact he.2.2.2.1
  · rw [hS]
    exact he.2.2.2.2.1
  · rw [hS]
    exact he.2.2.2.2.2

end HexagonPaper
