module
public import FourPapersCommon.FiniteCascadeGaussianSpinIntegral
public import FourPapersCommon.FiniteStateScalarRootGaussian

@[expose] public section

/-! The normalized terminal-feature Gaussian row is the physical spin
genealogy with that independent Gaussian coordinate in its root disorder.
All exponential-integrability and Fubini conditions are discharged. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy FiniteCascadeGenealogy FRSB
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem finiteCascadeTreeGaussianRowNormalizer_physical (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s c : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    finiteCascadeTreeGaussianRowNormalizer V K a L s (c^2) T R H =
      finiteCascadeTreeGaussianNormalizer V a L s j
        (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H := by
  have := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L (asGenealogy T)
  have hn (θ : ℝ) : finiteCascadeTreeFeatureNumerator V K a L s T R H (fun _ => 1) θ =
      ∫Q,Real.exp (s*finiteStateGaussianTerminalCascade V a L j (Q+θ • K))
        ∂finiteStateGaussianRawKernel R H := by
    have he := finiteCascadeTreeFeatureNumerator_spins V K a ha L s θ T R H
      (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => by norm_num)
    simpa only [integral_const, probReal_univ, smul_eq_mul,
      one_mul, mul_one] using he
  have hm := ((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.const_mul s).exp
  have hi := integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s j
    (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H
  unfold finiteCascadeTreeGaussianRowNormalizer gaussianHeatFlow
  simp only [zero_add, hn]
  exact (integral_finiteStateGaussianRawKernel_scalar_split R K H c _ hm hi).symm

theorem integral_finiteCascadeTreeGaussianRowLaw_physical_spins (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (hanti : Antitone a) (h0 : a 0 ≤ 1)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s c : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hs : s ≤ finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (B : ℝ) (hB : 0 ≤ B) (hK : ∀σ,|K σ| ≤ B)
    (F : Samples S (asGenealogy T) → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C) :
    (∫z,F (spins T z.2.2) ∂finiteCascadeTreeGaussianRowLaw V K a L s (c^2) T R H) =
      ∫z,F (spins T z.2) ∂finiteCascadeTreeGaussianJointLaw V a L s T
        (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H := by
  have := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L (asGenealogy T)
  let g : FiniteStateField S → ℝ :=
    fun Q => ∫σ,F σ ∂finiteCascadeGenealogyKernel V a L (asGenealogy T) Q
  have hgm : Measurable g := hF.stronglyMeasurable.integral_kernel.measurable
  have hgb (Q : FiniteStateField S) : ‖g Q‖ ≤ C := by
    simpa only [g, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ:=finiteCascadeGenealogyKernel V a L (asGenealogy T) Q)
        (f:=F) (C:=C)
        (.of_forall fun σ => by simpa only [Real.norm_eq_abs] using hFb σ))
  let f : FiniteStateField S → ℝ :=
    fun Q => Real.exp (s*finiteStateGaussianTerminalCascade V a L j Q)*g Q
  have hfm : Measurable f :=
    (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.const_mul s).exp).mul hgm
  have hi : Integrable f (finiteStateGaussianRawKernel
      (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H) := by
    apply ((integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s j
      (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H).mul_const C).mono'
      hfm.aestronglyMeasurable
    exact .of_forall fun Q => by
      dsimp only [f]
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hgb Q) (Real.exp_pos _).le
  rw [integral_finiteCascadeTreeGaussianRowLaw_spins V K a ha hanti h0 L s (c^2)
    T hs R H B hB hK F hF C hC hFb,
    integral_finiteCascadeTreeGaussianJointLaw_spins V a ha L s T
      (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H F hF C hC hFb,
    finiteCascadeTreeGaussianRowNormalizer_physical V K a ha L s c T R H]
  congr 1
  simp only [gaussianHeatFlow, zero_add]
  change (∫θ,(∫Q,f (Q+θ • K) ∂finiteStateGaussianRawKernel R H)
    ∂gaussianReal 0 (c^2).toNNReal) = ∫Q,f Q ∂finiteStateGaussianRawKernel
      (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H
  exact (integral_finiteStateGaussianRawKernel_scalar_split R K H c f hfm hi).symm

end FourPapersCommon
