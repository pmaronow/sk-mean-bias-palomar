module
public import HexagonPaper.PathHeatContinuousSignedSource
public import HexagonPaper.PathHeatFlatClockCoupling
public import HexagonPaper.PathHeatGeneralGaussianEnvelope

@[expose] public section

/-! Concrete moving-parameter dominated limits on the actual independent
canonical-Wiener reference. The path and kernel approximations are the
proved finite-edge Bernstein maps; the common envelope is the actual
Gaussian/Fernique envelope. Finite Price differentiation is a separate
input only to the eventual derivative-limit assembly. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {Z E K : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable (L : ℕ)

abbrev pathHeatWienerSourceSpace := Z×((E×K)×C(Fin L×I,ℝ))

def pathHeatWienerSourceState
    (c : Z→Fin L→C(I,I)) (T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ))
    (z : Z) (ω : pathHeatGeneralBaseSample E (Fin L) K) : pathHeatWienerSourceSpace (Z:=Z) (E:=E) (K:=K) L :=
  (z,((ω.1.1,ω.2),T (pathHeatFlatClockPath L (c z) ω.1.2)))

def pathHeatWienerSourceApproximateState
    (c : Z→Fin L→C(I,I)) (T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ))
    (n : ℕ) (z : Z) (ω : pathHeatGeneralBaseSample E (Fin L) K) : pathHeatWienerSourceSpace (Z:=Z) (E:=E) (K:=K) L :=
  (z,((ω.1.1,ω.2),T (pathHeatTreeBernsteinOperator n L (pathHeatFlatClockPath L (c z) ω.1.2))))

theorem continuous_pathHeatWienerSourceState
    (c : Z→Fin L→C(I,I)) (T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ)) (z : Z) :
    Continuous (pathHeatWienerSourceState (E:=E) (K:=K) L c T z) := by
  have hp := T.continuous.comp ((continuous_pathHeatFlatClockPath_Wiener L (c z)).comp
    (continuous_fst.snd : Continuous (fun ω : pathHeatGeneralBaseSample E (Fin L) K=>ω.1.2)))
  exact continuous_const.prodMk ((continuous_fst.fst.prodMk continuous_snd).prodMk hp)

theorem continuous_pathHeatWienerSourceApproximateState
    (c : Z→Fin L→C(I,I)) (T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ)) (n : ℕ) (z : Z) :
    Continuous (pathHeatWienerSourceApproximateState (E:=E) (K:=K) L c T n z) := by
  have hp := T.continuous.comp ((pathHeatTreeBernsteinOperator (E:=ℝ) n L).continuous.comp
    ((continuous_pathHeatFlatClockPath_Wiener L (c z)).comp
      (continuous_fst.snd : Continuous (fun ω : pathHeatGeneralBaseSample E (Fin L) K=>ω.1.2))))
  exact continuous_const.prodMk ((continuous_fst.fst.prodMk continuous_snd).prodMk hp)

theorem tendsto_pathHeatWienerSourceApproximateState
    (c : Z→Fin L→C(I,I)) (T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ))
    (hc : ∀l,Continuous (fun z=>c z l)) (z : ℕ→Z) (z₀ : Z)
    (hz : Tendsto z atTop (𝓝 z₀)) (ω : pathHeatGeneralBaseSample E (Fin L) K) :
    Tendsto (fun n=>pathHeatWienerSourceApproximateState L c T n (z n) ω) atTop
      (𝓝 (pathHeatWienerSourceState L c T z₀ ω)) := by
  have hp := T.continuous.continuousAt.tendsto.comp
    (tendsto_pathHeatFlatClockPath_Bernstein_moving L (fun n=>c (z n)) (c z₀) ω.1.2
      (fun l=>(hc l).continuousAt.tendsto.comp hz))
  exact hz.prodMk_nhds (tendsto_const_nhds.prodMk_nhds hp)

def pathHeatWienerSourceKernel
    (A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)))
    (D : Z→C(Fin L×I,C(Fin L×I,ℝ))) (z : Z) : ((Fin L×I)×(Fin L×I))→ᵇℝ :=
  pathHeatTreeKernelBCF L (A (D z))

def pathHeatWienerSourceApproximateKernel
    (A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)))
    (D : Z→C(Fin L×I,C(Fin L×I,ℝ))) (n : ℕ) (z : Z) : ((Fin L×I)×(Fin L×I))→ᵇℝ :=
  pathHeatTreeKernelBCF L (A (pathHeatTreeKernelSample n L (D z)))

theorem tendsto_pathHeatWienerSourceApproximateKernel
    (A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)))
    (D : Z→C(Fin L×I,C(Fin L×I,ℝ))) (hD : Continuous D)
    (z : ℕ→Z) (z₀ : Z) (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun n=>pathHeatWienerSourceApproximateKernel L A D n (z n)) atTop
      (𝓝 (pathHeatWienerSourceKernel L A D z₀)) :=
  (pathHeatTreeKernelBCF L).continuous.continuousAt.tendsto.comp
    (A.continuous.continuousAt.tendsto.comp
      (tendsto_pathHeatTreeKernelSample_moving L (fun n=>D (z n)) (D z₀)
        (hD.continuousAt.tendsto.comp hz)))

theorem norm_pathHeatWienerSourceKernel_le
    (A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)))
    (D : Z→C(Fin L×I,C(Fin L×I,ℝ))) (κA κ : ℝ≥0)
    (hA : ∀K,‖A K‖≤κA*‖K‖) (hD : ∀z,‖D z‖≤κ) (z : Z) :
    ‖pathHeatWienerSourceKernel L A D z‖≤(κA*κ:ℝ≥0) :=
  (norm_pathHeatTreeKernelBCF_le L _).trans ((hA _).trans
    (by simpa using mul_le_mul_of_nonneg_left (hD z) κA.coe_nonneg))

theorem norm_pathHeatWienerSourceApproximateKernel_le
    (A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)))
    (D : Z→C(Fin L×I,C(Fin L×I,ℝ))) (κA κ : ℝ≥0)
    (hA : ∀K,‖A K‖≤κA*‖K‖) (hD : ∀z,‖D z‖≤κ) (n : ℕ) (z : Z) :
    ‖pathHeatWienerSourceApproximateKernel L A D n z‖≤(κA*κ:ℝ≥0) :=
  (norm_pathHeatTreeKernelBCF_le L _).trans ((hA _).trans
    (by simpa using mul_le_mul_of_nonneg_left ((norm_pathHeatTreeKernelSample_le n L _).trans (hD z)) κA.coe_nonneg))

theorem pathHeatWienerSource_dominatedData
    (μ : Measure E) [IsGaussian μ]
    (d : PathHeatContinuousSignedSource (pathHeatWienerSourceSpace (Z:=Z) (E:=E) (K:=K) L) (Fin L×I))
    (c : Z→Fin L→C(I,I)) (T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ))
    (A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)))
    (D : Z→C(Fin L×I,C(Fin L×I,ℝ))) (κA κ C : ℝ≥0)
    (hA : ∀K,‖A K‖≤κA*‖K‖)
    (hD : ∀z,‖D z‖≤κ)
    (hgrowth : ∀z a k p,|d.ell (z,((a,k),p))|≤C*(1+‖a‖+‖p‖)) (z : Z) :
    PathHeatDominatedData (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
      (fun ω=>d.weight (pathHeatWienerSourceState L c T z ω))
      (fun ω=>d.phi (pathHeatWienerSourceState L c T z ω))
      (fun ω=>d.densityGenerator (pathHeatWienerSourceKernel L A D z) (pathHeatWienerSourceState L c T z ω))
      (fun ω=>d.observableGenerator (pathHeatWienerSourceKernel L A D z) (pathHeatWienerSourceState L c T z ω))
      (pathHeatGeneralEnvelope (C*(1+‖T‖))) d.B (d.densityBound (κA*κ)) (d.observableBound (κA*κ)) := by
  apply d.dominatedData _ _ _ (κA*κ)
    (continuous_pathHeatWienerSourceState L c T z).measurable
    (norm_pathHeatWienerSourceKernel_le L A D κA κ hA hD z)
    (pathHeatGeneralEnvelope (C*(1+‖T‖)))
    (integrable_pathHeatGeneralEnvelope_uniform (J:=Fin L) (K:=K) μ _)
  apply pathHeatGeneral_linearGrowth_envelope
    (fun ω=>T (pathHeatFlatClockPath L (c z) ω.1.2))
    (fun ω=>d.ell (pathHeatWienerSourceState L c T z ω)) C ‖T‖ C.coe_nonneg (norm_nonneg T)
  · intro ω
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_pathHeatFlatClockPath_le L _ _) (norm_nonneg T))
  · intro ω
    exact hgrowth z ω.1.1 ω.2 _

theorem pathHeatWienerSource_approximate_dominatedData
    (μ : Measure E) [IsGaussian μ]
    (d : PathHeatContinuousSignedSource (pathHeatWienerSourceSpace (Z:=Z) (E:=E) (K:=K) L) (Fin L×I))
    (c : Z→Fin L→C(I,I)) (T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ))
    (A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)))
    (D : Z→C(Fin L×I,C(Fin L×I,ℝ))) (κA κ C : ℝ≥0)
    (hA : ∀K,‖A K‖≤κA*‖K‖)
    (hD : ∀z,‖D z‖≤κ)
    (hgrowth : ∀z a k p,|d.ell (z,((a,k),p))|≤C*(1+‖a‖+‖p‖)) (n : ℕ) (z : Z) :
    PathHeatDominatedData (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
      (fun ω=>d.weight (pathHeatWienerSourceApproximateState L c T n z ω))
      (fun ω=>d.phi (pathHeatWienerSourceApproximateState L c T n z ω))
      (fun ω=>d.densityGenerator (pathHeatWienerSourceApproximateKernel L A D n z) (pathHeatWienerSourceApproximateState L c T n z ω))
      (fun ω=>d.observableGenerator (pathHeatWienerSourceApproximateKernel L A D n z) (pathHeatWienerSourceApproximateState L c T n z ω))
      (pathHeatGeneralEnvelope (C*(1+‖T‖))) d.B (d.densityBound (κA*κ)) (d.observableBound (κA*κ)) := by
  apply d.dominatedData _ _ _ (κA*κ)
    (continuous_pathHeatWienerSourceApproximateState L c T n z).measurable
    (norm_pathHeatWienerSourceApproximateKernel_le L A D κA κ hA hD n z)
    (pathHeatGeneralEnvelope (C*(1+‖T‖)))
    (integrable_pathHeatGeneralEnvelope_uniform (J:=Fin L) (K:=K) μ _)
  apply pathHeatGeneral_linearGrowth_envelope
    (fun ω=>T (pathHeatTreeBernsteinOperator n L (pathHeatFlatClockPath L (c z) ω.1.2)))
    (fun ω=>d.ell (pathHeatWienerSourceApproximateState L c T n z ω)) C ‖T‖ C.coe_nonneg (norm_nonneg T)
  · intro ω
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((norm_pathHeatTreeBernsteinSample_le n L _).trans (norm_pathHeatFlatClockPath_le L _ _)) (norm_nonneg T))
  · intro ω
    exact hgrowth z ω.1.1 ω.2 _

theorem pathHeatWienerSource_moving_values
    (d : PathHeatContinuousSignedSource (pathHeatWienerSourceSpace (Z:=Z) (E:=E) (K:=K) L) (Fin L×I))
    (c : Z→Fin L→C(I,I)) (T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ))
    (A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)))
    (D : Z→C(Fin L×I,C(Fin L×I,ℝ)))
    (hc : ∀l,Continuous (fun z=>c z l)) (hD : Continuous D)
    (z : ℕ→Z) (z₀ : Z) (hz : Tendsto z atTop (𝓝 z₀))
    (ω : pathHeatGeneralBaseSample E (Fin L) K) :
    Tendsto (fun n=>d.weight (pathHeatWienerSourceApproximateState L c T n (z n) ω)) atTop
      (𝓝 (d.weight (pathHeatWienerSourceState L c T z₀ ω))) ∧
    Tendsto (fun n=>d.phi (pathHeatWienerSourceApproximateState L c T n (z n) ω)) atTop
      (𝓝 (d.phi (pathHeatWienerSourceState L c T z₀ ω))) ∧
    Tendsto (fun n=>d.densityGenerator (pathHeatWienerSourceApproximateKernel L A D n (z n))
      (pathHeatWienerSourceApproximateState L c T n (z n) ω)) atTop
      (𝓝 (d.densityGenerator (pathHeatWienerSourceKernel L A D z₀) (pathHeatWienerSourceState L c T z₀ ω))) ∧
    Tendsto (fun n=>d.observableGenerator (pathHeatWienerSourceApproximateKernel L A D n (z n))
      (pathHeatWienerSourceApproximateState L c T n (z n) ω)) atTop
      (𝓝 (d.observableGenerator (pathHeatWienerSourceKernel L A D z₀) (pathHeatWienerSourceState L c T z₀ ω))) :=
  d.moving_values _ _ _ _
    (tendsto_pathHeatWienerSourceApproximateState L c T hc z z₀ hz ω)
    (tendsto_pathHeatWienerSourceApproximateKernel L A D hD z z₀ hz)

theorem pathHeatWienerSource_moving_values_succ
    (d : PathHeatContinuousSignedSource (pathHeatWienerSourceSpace (Z:=Z) (E:=E) (K:=K) L) (Fin L×I))
    (c : Z→Fin L→C(I,I)) (T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ))
    (A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)))
    (D : Z→C(Fin L×I,C(Fin L×I,ℝ)))
    (hc : ∀l,Continuous (fun z=>c z l)) (hD : Continuous D)
    (z : ℕ→Z) (z₀ : Z) (hz : Tendsto z atTop (𝓝 z₀))
    (ω : pathHeatGeneralBaseSample E (Fin L) K) :
    Tendsto (fun n=>d.weight (pathHeatWienerSourceApproximateState L c T (n+1) (z n) ω)) atTop
      (𝓝 (d.weight (pathHeatWienerSourceState L c T z₀ ω))) ∧
    Tendsto (fun n=>d.phi (pathHeatWienerSourceApproximateState L c T (n+1) (z n) ω)) atTop
      (𝓝 (d.phi (pathHeatWienerSourceState L c T z₀ ω))) ∧
    Tendsto (fun n=>d.densityGenerator (pathHeatWienerSourceApproximateKernel L A D (n+1) (z n))
      (pathHeatWienerSourceApproximateState L c T (n+1) (z n) ω)) atTop
      (𝓝 (d.densityGenerator (pathHeatWienerSourceKernel L A D z₀) (pathHeatWienerSourceState L c T z₀ ω))) ∧
    Tendsto (fun n=>d.observableGenerator (pathHeatWienerSourceApproximateKernel L A D (n+1) (z n))
      (pathHeatWienerSourceApproximateState L c T (n+1) (z n) ω)) atTop
      (𝓝 (d.observableGenerator (pathHeatWienerSourceKernel L A D z₀) (pathHeatWienerSourceState L c T z₀ ω))) := by
  have hv := pathHeatWienerSource_moving_values L d c T A D hc hD
    (fun n=>z (n-1)) z₀ (hz.comp (tendsto_sub_atTop_nat 1)) ω
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.1.comp (tendsto_add_atTop_nat 1)
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.2.1.comp (tendsto_add_atTop_nat 1)
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.2.2.1.comp (tendsto_add_atTop_nat 1)
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.2.2.2.comp (tendsto_add_atTop_nat 1)

end HexagonPaper
