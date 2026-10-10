module
public import FourPapersCommon.FiniteCascadeTreeFeatureBounds

@[expose] public section

/-! Bounds for a uniformly bounded terminal observable use its pointwise
bound, not its Euclidean norm on the whole configuration space. In
particular binary spin features have dimension-independent constant one. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteCascadeFeature_first_abs_le_of_pointwise (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) (C : ℝ) (hK : ∀σ,|K σ|≤C) :
    |fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H K|≤C := by
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
  rw [fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L j]
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono Integrable.of_finite (integrable_const C) hK).trans_eq
  simp

theorem finiteCascadeFeature_second_abs_le_of_pointwise (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C) :
    |fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H K K|≤C^2 := by
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
  rw [abs_of_nonneg (finiteStateCascadeHessian_nonneg V a ha L j H K)]
  apply (finiteStateCascadeHessian_covariance_bounds V a ha
    (fun i=>(hanti (Nat.zero_le i)).trans h0) (fun i=>hanti (Nat.le_succ i)) L j H K).2.trans
  rw [finiteStateCascadeObservableVariance_eq_variance V a ha L j H K]
  apply (variance_le_expectation_sq (measurable_of_finite _).aestronglyMeasurable).trans
  calc
    _≤∫_ : S,C^2 ∂finiteStateCascadeGibbsKernel V a L j H := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro σ
      simpa only [sq_abs,Pi.pow_apply] using pow_le_pow_left₀ (abs_nonneg (K σ)) (hK σ) 2
    _=_ := by simp

theorem finiteCascadeTreeTerminalFeature_abs_le_of_pointwise (K : FiniteStateField S)
    (C : ℝ) (hK : ∀σ,|K σ|≤C)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records (FiniteStateField S) S T) :
    |finiteCascadeTreeTerminalFeature K T z|≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*C := by
  induction T with
  | leaf => simpa [finiteCascadeTreeTerminalFeature,asGenealogy,
      FiniteCascadeGenealogy.leafCount] using hK z
  | advance T ih => exact ih z.2
  | fork T U ihT ihU =>
      calc
        _≤|finiteCascadeTreeTerminalFeature K T z.1|+
            |finiteCascadeTreeTerminalFeature K U z.2| := abs_add_le _ _
        _≤(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*C+
            (FiniteCascadeGenealogy.leafCount (asGenealogy U):ℝ)*C :=
          add_le_add (ihT z.1) (ihU z.2)
        _=_ := by simp only [asGenealogy,FiniteCascadeGenealogy.leafCount,Nat.cast_add];ring

theorem finiteCascadeTreeFeatureScore_abs_le_of_pointwise (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (H K : FiniteStateField S) (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    |finiteCascadeTreeFeatureScore V a L s T H K z θ|≤
      (2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C := by
  have hb := finiteCascadeTreeFieldSum_abs_le a ha hanti h0
    (fun j Q=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) Q K)
    C hC (fun j Q=>finiteCascadeFeature_first_abs_le_of_pointwise V a ha L j Q K C hK)
    s T hs (H+θ • K) (finiteCascadeShiftRecords K θ T z)
  calc
    _≤|finiteCascadeTreeTerminalFeature K T z|+
        |finiteCascadeTreeFieldSum a
          (fun j Q=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) Q K)
          s T (H+θ • K) (finiteCascadeShiftRecords K θ T z)| := abs_sub _ _
    _≤(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*C+
        ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C :=
      add_le_add (finiteCascadeTreeTerminalFeature_abs_le_of_pointwise K C hK T z) hb
    _=_ := by ring

theorem finiteCascadeTreeFeatureSecondCharge_abs_le_of_pointwise (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (H K : FiniteStateField S) (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    |finiteCascadeTreeFeatureSecondCharge V a L s T H K z θ|≤
      ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2 := by
  exact finiteCascadeTreeFieldSum_abs_le a ha hanti h0 _ (C^2) (sq_nonneg _) 
    (fun j Q=>finiteCascadeFeature_second_abs_le_of_pointwise V a ha hanti h0 L j Q K C hC hK)
    s T hs (H+θ • K) (finiteCascadeShiftRecords K θ T z)

end FourPapersCommon
