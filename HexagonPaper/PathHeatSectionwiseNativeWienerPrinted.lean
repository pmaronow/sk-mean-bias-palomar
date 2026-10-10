module
public import HexagonPaper.PathHeatSectionwiseNativeWienerModel
public import HexagonPaper.PathHeatSectionwiseWienerLimit
public import HexagonPaper.PathHeatSectionwisePrintedResponse
public import HexagonPaper.PathHeatCountingNormalization

@[expose] public section

/-! Exact printed response on the actual native compact index and genuine
Gaussian × independent canonical Wiener × finite counting reference.
Measurability, covariance bounds and the common Fernique envelope are
derived internally from the native source. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal ENNReal BoundedContinuousFunction
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 2000000
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

theorem measurable_pathHeatSectionwiseNativeWienerState (ι : C(X,Fin L×I))
    (c : Icc a b→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (z : Icc a b) :
    Measurable (pathHeatSectionwiseNativeWienerState (E:=E) (K:=K) ι c δ W z) := by
  exact ((continuous_pathHeatNativeSourceRestrictionState ι).comp
    (continuous_pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z)).measurable

theorem norm_pathHeatSectionwiseNativeWienerKernel_le (ι : C(X,Fin L×I))
    (dc : Icc a b→Fin L→C(I,ℝ)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (κ : ℝ≥0) (hκ : ∀z,‖pathHeatClockRawKernel (dc z)‖≤κ) (z : Icc a b) :
    ‖pathHeatSectionwiseNativeWienerKernel ι dc δ W z‖ ≤ (pathHeatTreeMixedBound δ W)^2*κ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (sq_nonneg _) κ.coe_nonneg)).mpr
  intro x
  change ‖pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (dc z))
    (ι x.1) (ι x.2)‖ ≤ _
  exact (((pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (dc z))
    (ι x.1)).norm_coe_le_norm (ι x.2)).trans
    ((pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (dc z))).norm_coe_le_norm
      (ι x.1))).trans ((norm_pathHeatTreeMixedKernelOperator_apply_le δ W _).trans
        (mul_le_mul_of_nonneg_left (hκ z) (sq_nonneg _)))

theorem pathHeatSectionwiseNativeWiener_weight_envelope
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (C : ℝ≥0)
    (hgrowth : ∀z ω p,|d.ell (z,(ω,p))|≤C*(1+‖ω.1‖+‖p‖)) (z : Icc a b) :
    ∀ω,pathHeatSectionwiseNativeWienerWeight d ι c δ W z ω ≤
      pathHeatGeneralEnvelope (C*(1+‖pathHeatTreeMixedOperator (E:=ℝ) δ W‖)) ω := by
  apply pathHeatGeneral_linearGrowth_envelope
    (fun ω=>pathHeatIndexRestriction ι
      (pathHeatTreeMixedOperator δ W (pathHeatFlatClockPath L (c z) ω.1.2)))
    (fun ω=>d.ell (pathHeatSectionwiseNativeWienerState ι c δ W z ω)) C
    ‖pathHeatTreeMixedOperator (E:=ℝ) δ W‖ C.coe_nonneg
    (norm_nonneg (pathHeatTreeMixedOperator (E:=ℝ) δ W))
  · intro ω
    exact (pathHeatIndexRestriction_norm_apply_le ι _).trans
      (((pathHeatTreeMixedOperator (E:=ℝ) δ W).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_pathHeatFlatClockPath_le L _ _)
          (norm_nonneg (pathHeatTreeMixedOperator (E:=ℝ) δ W))))
  · intro ω
    exact hgrowth z (ω.1.1,ω.2) _

def pathHeatSectionwiseNativeWienerMean (μ : Measure E)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : Icc a b)
    (F : Icc a b×((E×K)×C(X,ℝ))→ℝ) : ℝ :=
  pathHeatExpectation (pathHeatGeneralCountMeasure (J:=Fin L) (K:=K) μ)
    (pathHeatSectionwiseNativeWienerWeight d ι c δ W z)
    (fun ω=>F (pathHeatSectionwiseNativeWienerState ι c δ W z ω))

theorem pathHeatSectionwiseNativeWienerMean_phi (μ : Measure E)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : Icc a b) :
    pathHeatSectionwiseNativeWienerMean μ d ι c δ W z d.phi =
      pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W z := rfl

theorem pathHeatSectionwiseNativeWiener_uniform_dominatedData
    (μ : Measure E) [IsGaussian μ]
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (dc : Icc a b→Fin L→C(I,ℝ)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hab : a≤b) (C : ℝ≥0) (hsource : PathHeatSectionwiseAnalyticSource a b hab d C)
    (κ : ℝ≥0) (hκ : ∀z,‖pathHeatClockRawKernel (dc z)‖≤κ) (z : Icc a b) :
    PathHeatDominatedData (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
      (pathHeatSectionwiseNativeWienerWeight d ι c δ W z)
      (fun ω=>d.phi (pathHeatSectionwiseNativeWienerState ι c δ W z ω))
      (fun ω=>d.densityGenerator (pathHeatSectionwiseNativeWienerKernel ι dc δ W z)
        (pathHeatSectionwiseNativeWienerState ι c δ W z ω))
      (fun ω=>d.observableGenerator (pathHeatSectionwiseNativeWienerKernel ι dc δ W z)
        (pathHeatSectionwiseNativeWienerState ι c δ W z ω))
      (pathHeatGeneralEnvelope (C*(1+‖pathHeatTreeMixedOperator (E:=ℝ) δ W‖))) d.B
      (d.densityBound (pathHeatWienerMixedKernelBound δ W*κ))
      (d.observableBound (pathHeatWienerMixedKernelBound δ W*κ)) := by
  have h := pathHeatSectionwiseWiener_actual_dominatedData μ hab
    (pathHeatSectionwiseNativeSourceExtension ι d) C
    (pathHeatSectionwiseNativeSourceExtension_analytic hab ι d C hsource)
    c δ W (fun z=>pathHeatClockRawKernel (dc z)) κ hκ z
  have hk : pathHeatNativeKernelRestriction ι
      (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W)
        (fun z=>pathHeatClockRawKernel (dc z)) z) =
      pathHeatSectionwiseNativeWienerKernel ι dc δ W z := by
    ext x
    rfl
  simp_rw [pathHeatSectionwiseNativeSourceExtension_densityGenerator,
    pathHeatSectionwiseNativeSourceExtension_observableGenerator,hk] at h
  exact h

theorem pathHeatSectionwiseNativeWienerResponse_printed (μ : Measure E) [IsGaussian μ]
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (dc : Icc a b→Fin L→C(I,ℝ)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hab : a≤b) (C : ℝ≥0) (hsource : PathHeatSectionwiseAnalyticSource a b hab d C)
    (hdc : ∀l,Continuous (fun z=>dc z l)) (z : Icc a b) :
    pathHeatSectionwiseNativeWienerResponse μ d ι c dc δ W z =
      pathHeatSectionwiseNativeWienerMean μ d ι c δ W z d.dotphi+
      (pathHeatSectionwiseNativeWienerMean μ d ι c δ W z (fun θ=>d.phi θ*d.dotell θ)-
        pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W z*
          pathHeatSectionwiseNativeWienerMean μ d ι c δ W z d.dotell)+
      (1/2:ℝ)*pathHeatSectionwiseNativeWienerMean μ d ι c δ W z
        (d.centeredContraction (pathHeatSectionwiseNativeWienerKernel ι dc δ W z)
          (pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W z)) := by
  obtain ⟨κ,hκ⟩ := exists_pathHeatClockRawKernel_bound_of_continuous dc hdc
  have h := pathHeatSectionwiseNativeWiener_uniform_dominatedData μ d ι c dc δ W
    hab C hsource κ hκ z
  have hp := d.normalized_response_printed
    (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (pathHeatSectionwiseNativeWienerState ι c δ W z)
    (pathHeatSectionwiseNativeWienerKernel ι dc δ W z)
    (measurable_pathHeatSectionwiseNativeWienerState ι c δ W z)
    (pathHeatGeneralEnvelope (C*(1+‖pathHeatTreeMixedOperator (E:=ℝ) δ W‖)))
    (d.densityBound (pathHeatWienerMixedKernelBound δ W*κ))
    (d.observableBound (pathHeatWienerMixedKernelBound δ W*κ)) h
  unfold pathHeatSectionwiseNativeWienerResponse pathHeatSectionwiseNativeWienerMean pathHeatSectionwiseNativeWienerExpectation
  rw [pathHeatGeneralCountMeasure_eq_card_smul_uniform]
  simp only [pathHeatExpectation_nat_smul _ _ _ _ Fintype.card_ne_zero,
    pathHeatResponse_nat_smul _ _ _ _ _ _ Fintype.card_ne_zero]
  exact hp

theorem pathHeatSectionwiseNativeWienerLogNormalizerResponse_printed (μ : Measure E) [IsGaussian μ]
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (dc : Icc a b→Fin L→C(I,ℝ)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hab : a≤b) (C : ℝ≥0) (hsource : PathHeatSectionwiseAnalyticSource a b hab d C)
    (hdc : ∀l,Continuous (fun z=>dc z l)) (z : Icc a b) :
    pathHeatSectionwiseNativeWienerLogNormalizerResponse μ d ι c dc δ W z =
      pathHeatSectionwiseNativeWienerMean μ d ι c δ W z d.dotell+
      (1/2:ℝ)*pathHeatSectionwiseNativeWienerMean μ d ι c δ W z
        (d.densityContraction (pathHeatSectionwiseNativeWienerKernel ι dc δ W z)) := by
  obtain ⟨κ,hκ⟩ := exists_pathHeatClockRawKernel_bound_of_continuous dc hdc
  have h := pathHeatSectionwiseNativeWiener_uniform_dominatedData μ d ι c dc δ W
    hab C hsource κ hκ z
  have hp := d.normalized_densityGenerator_printed
    (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (pathHeatSectionwiseNativeWienerState ι c δ W z)
    (pathHeatSectionwiseNativeWienerKernel ι dc δ W z)
    (measurable_pathHeatSectionwiseNativeWienerState ι c δ W z)
    (pathHeatGeneralEnvelope (C*(1+‖pathHeatTreeMixedOperator (E:=ℝ) δ W‖)))
    (d.densityBound (pathHeatWienerMixedKernelBound δ W*κ))
    (d.observableBound (pathHeatWienerMixedKernelBound δ W*κ)) h
  unfold pathHeatSectionwiseNativeWienerLogNormalizerResponse pathHeatSectionwiseNativeWienerMean
  rw [pathHeatGeneralCountMeasure_eq_card_smul_uniform]
  simp only [pathHeatExpectation_nat_smul _ _ _ _ Fintype.card_ne_zero,
    pathHeatResponse_nat_smul _ _ _ _ _ _ Fintype.card_ne_zero]
  exact hp

end HexagonPaper
