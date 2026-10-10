module
public import HexagonPaper.PathHeatWienerDifferentiation
public import HexagonPaper.PathHeatAuxiliaryGeneralGaussianUniform

@[expose] public section

/-! Actual finite counting measure, its positive mass and the exact
invariance of normalized heat formulas under counting normalization. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal ENNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem pathHeatNormalizer_nat_smul (μ : Measure Ω) (W : Ω→ℝ) (n : ℕ) :
    pathHeatNormalizer ((n:ℝ≥0∞)•μ) W=(n:ℝ)*pathHeatNormalizer μ W := by
  simp only [pathHeatNormalizer,integral_smul_measure,ENNReal.toReal_natCast,smul_eq_mul]

theorem pathHeatExpectation_nat_smul (μ : Measure Ω) (W F : Ω→ℝ) (n : ℕ) (hn : n≠0) :
    pathHeatExpectation ((n:ℝ≥0∞)•μ) W F=pathHeatExpectation μ W F := by
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn
  simp only [pathHeatExpectation,pathHeatNormalizer_nat_smul,integral_smul_measure,
    ENNReal.toReal_natCast,smul_eq_mul]
  exact mul_div_mul_left _ _ hnr

theorem pathHeatResponse_nat_smul (μ : Measure Ω) (W F H J : Ω→ℝ) (n : ℕ) (hn : n≠0) :
    pathHeatResponse ((n:ℝ≥0∞)•μ) W F H J=pathHeatResponse μ W F H J := by
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn
  simp only [pathHeatResponse,pathHeatExpectation_nat_smul μ W F n hn,
    pathHeatNormalizer_nat_smul,integral_smul_measure,ENNReal.toReal_natCast,smul_eq_mul]
  exact mul_div_mul_left _ _ hnr

theorem hasDerivAt_pathHeat_nat_counting_normalization
    (μ : Measure Ω) (W F H J : ℝ→Ω→ℝ) (n : ℕ) (hn : n≠0) (x : ℝ)
    (hp : ∀u,0<pathHeatNormalizer μ (W u))
    (hE : HasDerivAt (fun u=>pathHeatExpectation μ (W u) (F u))
      (pathHeatResponse μ (W x) (F x) (H x) (J x)) x)
    (hlog : HasDerivAt (fun u=>Real.log (pathHeatNormalizer μ (W u)))
      (pathHeatExpectation μ (W x) (H x)) x) :
    (0<pathHeatNormalizer ((n:ℝ≥0∞)•μ) (W x)) ∧
    HasDerivAt (fun u=>pathHeatExpectation ((n:ℝ≥0∞)•μ) (W u) (F u))
      (pathHeatResponse ((n:ℝ≥0∞)•μ) (W x) (F x) (H x) (J x)) x ∧
    HasDerivAt (fun u=>Real.log (pathHeatNormalizer ((n:ℝ≥0∞)•μ) (W u)))
      (pathHeatExpectation ((n:ℝ≥0∞)•μ) (W x) (H x)) x := by
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn
  have hnp : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine ⟨?_,?_,?_⟩
  · rw [pathHeatNormalizer_nat_smul]
    exact mul_pos hnp (hp x)
  · simpa only [pathHeatExpectation_nat_smul μ _ _ n hn,
      pathHeatResponse_nat_smul μ _ _ _ _ n hn] using hE
  · have heq : (fun u=>Real.log (pathHeatNormalizer ((n:ℝ≥0∞)•μ) (W u)))=
        fun u=>Real.log (n:ℝ)+Real.log (pathHeatNormalizer μ (W u)) := by
      funext u
      rw [pathHeatNormalizer_nat_smul,Real.log_mul hnr (hp u).ne']
    rw [heq,pathHeatExpectation_nat_smul μ _ _ n hn]
    exact hlog.const_add (Real.log (n:ℝ))

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L : ℕ}

theorem pathHeatGeneralCountMeasure_eq_card_smul_uniform (μ : Measure E) [IsGaussian μ] :
    pathHeatGeneralCountMeasure (J:=Fin L) (K:=K) μ=
      (Fintype.card K:ℝ≥0∞)•pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ := by
  rw [pathHeatGeneralCountMeasure,pathHeat_count_eq_card_smul_uniform,
    Measure.prod_smul_right,pathHeatGeneralUniformMeasure]

theorem pathHeatGeneral_count_normalized_moments (μ : Measure E) [IsGaussian μ]
    (weight phi H J : pathHeatGeneralBaseSample E (Fin L) K→ℝ) :
    pathHeatNormalizer (pathHeatGeneralCountMeasure μ) weight=
      (Fintype.card K:ℝ)*pathHeatNormalizer (pathHeatGeneralUniformMeasure μ) weight ∧
    pathHeatExpectation (pathHeatGeneralCountMeasure μ) weight phi=
      pathHeatExpectation (pathHeatGeneralUniformMeasure μ) weight phi ∧
    pathHeatResponse (pathHeatGeneralCountMeasure μ) weight phi H J=
      pathHeatResponse (pathHeatGeneralUniformMeasure μ) weight phi H J := by
  rw [pathHeatGeneralCountMeasure_eq_card_smul_uniform]
  exact ⟨pathHeatNormalizer_nat_smul _ _ _,
    pathHeatExpectation_nat_smul _ _ _ _ Fintype.card_ne_zero,
    pathHeatResponse_nat_smul _ _ _ _ _ _ Fintype.card_ne_zero⟩

end HexagonPaper
