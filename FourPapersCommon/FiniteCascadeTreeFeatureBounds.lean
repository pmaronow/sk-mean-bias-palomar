module
public import FourPapersCommon.FiniteCascadeTreeFeatureScores
public import FourPapersCommon.FiniteStateCascadeCovarianceComparison

@[expose] public section

/-! Genuine uniform feature-score bounds from the actual nonnegative
vertex charges. These bounds are independent of the fields, Gaussian
maps and cascade depth. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteCascadeTreeInteriorFieldSum_abs_le (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (F : ℕ→FiniteStateField S→ℝ) (C : ℝ) (hC : 0≤C)
    (hF : ∀j H,|F j H|≤C) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : Records (FiniteStateField S) S T) :
    |finiteCascadeTreeInteriorFieldSum a F T z|≤
      ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-
        finiteCascadeTreeRootCoefficient a T)*C := by
  induction T with
  | leaf => simp [finiteCascadeTreeInteriorFieldSum,finiteCascadeTreeRootCoefficient,
      asGenealogy,FiniteCascadeGenealogy.leafCount]
  | @advance j T ih =>
      have hc : 0≤finiteCascadeTreeRootCoefficient a T-a j :=
        sub_nonneg.mpr (finiteCascadeTreeRootCoefficient_ge a ha hanti h0 T)
      calc
        _≤|(finiteCascadeTreeRootCoefficient a T-a j)*F j z.1|+
            |finiteCascadeTreeInteriorFieldSum a F T z.2| := abs_add_le _ _
        _≤(finiteCascadeTreeRootCoefficient a T-a j)*C+
            ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-
              finiteCascadeTreeRootCoefficient a T)*C :=
          add_le_add (by rw [abs_mul,abs_of_nonneg hc];exact mul_le_mul_of_nonneg_left (hF j z.1) hc) (ih z.2)
        _=_ := by simp only [asGenealogy,FiniteCascadeGenealogy.leafCount,
          finiteCascadeTreeRootCoefficient];ring
  | fork T U ihT ihU =>
      calc
        _≤|finiteCascadeTreeInteriorFieldSum a F T z.1|+
            |finiteCascadeTreeInteriorFieldSum a F U z.2| := abs_add_le _ _
        _≤((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-
              finiteCascadeTreeRootCoefficient a T)*C+
            ((FiniteCascadeGenealogy.leafCount (asGenealogy U):ℝ)-
              finiteCascadeTreeRootCoefficient a U)*C := add_le_add (ihT z.1) (ihU z.2)
        _=_ := by simp only [asGenealogy,FiniteCascadeGenealogy.leafCount,
          finiteCascadeTreeRootCoefficient,Nat.cast_add];ring

theorem finiteCascadeTreeFieldSum_abs_le (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (F : ℕ→FiniteStateField S→ℝ) (C : ℝ) (hC : 0≤C)
    (hF : ∀j H,|F j H|≤C) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (H : FiniteStateField S) (z : Records (FiniteStateField S) S T) :
    |finiteCascadeTreeFieldSum a F s T H z|≤
      ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C := by
  have hc : 0≤finiteCascadeTreeRootCoefficient a T-s := sub_nonneg.mpr hs
  calc
    _≤|(finiteCascadeTreeRootCoefficient a T-s)*F j H|+
        |finiteCascadeTreeInteriorFieldSum a F T z| := abs_add_le _ _
    _≤(finiteCascadeTreeRootCoefficient a T-s)*C+
        ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-
          finiteCascadeTreeRootCoefficient a T)*C :=
      add_le_add (by rw [abs_mul,abs_of_nonneg hc];exact mul_le_mul_of_nonneg_left (hF j H) hc)
        (finiteCascadeTreeInteriorFieldSum_abs_le a ha hanti h0 F C hC hF T z)
    _=_ := by ring

theorem finiteCascadeTreeTerminalFeature_abs_le (K : FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records (FiniteStateField S) S T) :
    |finiteCascadeTreeTerminalFeature K T z|≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*‖K‖ := by
  induction T with
  | leaf => simpa [finiteCascadeTreeTerminalFeature,asGenealogy,
      FiniteCascadeGenealogy.leafCount,Real.norm_eq_abs] using PiLp.norm_apply_le K z
  | advance T ih => exact ih z.2
  | fork T U ihT ihU =>
      calc
        _≤|finiteCascadeTreeTerminalFeature K T z.1|+
            |finiteCascadeTreeTerminalFeature K U z.2| := abs_add_le _ _
        _≤(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*‖K‖+
            (FiniteCascadeGenealogy.leafCount (asGenealogy U):ℝ)*‖K‖ :=
          add_le_add (ihT z.1) (ihU z.2)
        _=_ := by simp only [asGenealogy,FiniteCascadeGenealogy.leafCount,Nat.cast_add];ring

theorem finiteCascadeTreeFeatureScore_abs_le (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (H K : FiniteStateField S) (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    |finiteCascadeTreeFeatureScore V a L s T H K z θ|≤
      (2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*‖K‖ := by
  have hb := finiteCascadeTreeFieldSum_abs_le a ha hanti h0
    (fun j Q=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) Q K)
    ‖K‖ (norm_nonneg K) (fun j Q=>finiteStateCascadeFirst_abs_le V a ha L j Q K)
    s T hs (H+θ • K) (finiteCascadeShiftRecords K θ T z)
  calc
    _≤|finiteCascadeTreeTerminalFeature K T z|+
        |finiteCascadeTreeFieldSum a
          (fun j Q=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) Q K)
          s T (H+θ • K) (finiteCascadeShiftRecords K θ T z)| := abs_sub _ _
    _≤(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*‖K‖+
        ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*‖K‖ :=
      add_le_add (finiteCascadeTreeTerminalFeature_abs_le K T z) hb
    _=_ := by ring

theorem finiteCascadeTreeFeatureLogNumerator_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (H K : FiniteStateField S) (z : Records (FiniteStateField S) S T) :
    LipschitzWith (((2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*‖K‖).toNNReal)
      (finiteCascadeTreeFeatureLogNumerator V a L s T H K z) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun θ=>(hasDerivAt_finiteCascadeTreeFeatureLogNumerator V a ha L s T H K z θ).differentiableAt)
  intro θ
  apply (NNReal.coe_le_coe).mp
  rw [Real.coe_toNNReal _ ((abs_nonneg _).trans
    (finiteCascadeTreeFeatureScore_abs_le V a ha hanti h0 L s T hs H K z θ))]
  simpa only [coe_nnnorm,Real.norm_eq_abs,
    (hasDerivAt_finiteCascadeTreeFeatureLogNumerator V a ha L s T H K z θ).deriv] using
    finiteCascadeTreeFeatureScore_abs_le V a ha hanti h0 L s T hs H K z θ

theorem finiteCascadeFeature_second_abs_le (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    |fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H K K|≤‖K‖^2 := by
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
  rw [abs_of_nonneg (finiteStateCascadeHessian_nonneg V a ha L j H K)]
  apply (finiteStateCascadeHessian_covariance_bounds V a ha
    (fun i=>(hanti (Nat.zero_le i)).trans h0) (fun i=>hanti (Nat.le_succ i)) L j H K).2.trans
  rw [finiteStateCascadeObservableVariance_eq_variance V a ha L j H K]
  apply (variance_le_expectation_sq (measurable_of_finite _).aestronglyMeasurable).trans
  calc
    _≤∫_ : S,‖K‖^2 ∂finiteStateCascadeGibbsKernel V a L j H := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro σ
      simpa only [sq_abs,Pi.pow_apply] using pow_le_pow_left₀ (abs_nonneg (K σ))
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K σ) 2
    _=_ := by simp

theorem finiteCascadeTreeFeatureSecondCharge_abs_le (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (H K : FiniteStateField S) (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    |finiteCascadeTreeFeatureSecondCharge V a L s T H K z θ|≤
      ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*‖K‖^2 := by
  exact finiteCascadeTreeFieldSum_abs_le a ha hanti h0 _ (‖K‖^2) (sq_nonneg _) 
    (fun j Q=>finiteCascadeFeature_second_abs_le V a ha hanti h0 L j Q K)
    s T hs (H+θ • K) (finiteCascadeShiftRecords K θ T z)

end FourPapersCommon
