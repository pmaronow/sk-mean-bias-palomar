module
public import FourPapersCommon.FiniteCascadeGaussianRecordIntegral
public import FourPapersCommon.FiniteCascadeGaussianRowPhysical

@[expose] public section

/-! An independent Gaussian terminal-feature row gives the actual joint
law of every retained field and spin record after the physical translation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy FRSB
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem integral_finiteCascadeTreeGaussianRowLaw_physical_records (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (hanti : Antitone a) (h0 : a 0 ≤ 1)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s c : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hs : s ≤ finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (B : ℝ) (hB : 0 ≤ B) (hK : ∀σ,|K σ| ≤ B)
    (F : FiniteStateField S × Records (FiniteStateField S) S T → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C) :
    (∫z,F (z.2.1+z.1 • K,finiteCascadeShiftRecords K z.1 T z.2.2)
      ∂finiteCascadeTreeGaussianRowLaw V K a L s (c^2) T R H) =
      ∫z,F z ∂finiteCascadeTreeGaussianJointLaw V a L s T
        (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H := by
  have := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  let g : FiniteStateField S → ℝ :=
    fun Q => ∫z,F (Q,z) ∂finiteCascadeTreeRecordKernel V a L T Q
  have hgm : Measurable g := hF.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hgb (Q : FiniteStateField S) : ‖g Q‖ ≤ C := by
    simpa only [g,probReal_univ,mul_one] using
      (norm_integral_le_of_norm_le_const (μ:=finiteCascadeTreeRecordKernel V a L T Q)
        (f:=fun z => F (Q,z)) (C:=C)
        (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hFb (Q,z)))
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
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hgb Q) (Real.exp_pos _).le
  let G := fun z : ℝ × (FiniteStateField S × Records (FiniteStateField S) S T) =>
    F (z.2.1+z.1 • K,finiteCascadeShiftRecords K z.1 T z.2.2)
  have hG : Measurable G := hF.comp
    (((measurable_fst.comp measurable_snd).add (measurable_fst.smul_const K)).prodMk
      ((measurable_finiteCascadeShiftRecords_joint K T).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))
  have hIF : Integrable (fun z => Real.exp
      (finiteCascadeTreeGaussianRowLogNumerator V K a L s T z)*G z)
      (finiteCascadeTreeGaussianRowReference L (c^2) T R H) := by
    apply ((integrable_exp_finiteCascadeTreeGaussianRowLogNumerator V K a ha hanti h0 L s
      (c^2) T hs R H B hB hK).mul_const C).mono'
      (((measurable_finiteCascadeTreeGaussianRowLogNumerator V K a ha L s T).exp.mul hG).aestronglyMeasurable)
    exact .of_forall fun z => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hFb _) (Real.exp_pos _).le
  change (∫z,G z ∂finiteCascadeTreeGaussianRowLaw V K a L s (c^2) T R H) = _
  rw [finiteCascadeTreeGaussianRowLaw,integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div]
  rw [integral_div,integral_exp_finiteCascadeTreeGaussianRowLogNumerator
    V K a ha hanti h0 L s (c^2) T hs R H B hB hK,
    finiteCascadeTreeGaussianRowReference,integral_prod _ hIF,
    integral_finiteCascadeTreeGaussianJointLaw_records V a ha L s T
      (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H F hF C hFb,
    finiteCascadeTreeGaussianRowNormalizer_physical V K a ha L s c T R H]
  congr 1
  have hn (θ : ℝ) : (∫z,Real.exp
      (finiteCascadeTreeGaussianRowLogNumerator V K a L s T (θ,z))*G (θ,z)
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H) =
      ∫Q,f (Q+θ • K) ∂finiteStateGaussianRawKernel R H := by
    have hh := finiteCascadeTreeFeatureNumerator_records V K a ha L s θ T R H F hF C hFb
    change (∫z,Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)*
      F (z.1+θ • K,finiteCascadeShiftRecords K θ T z.2)
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H) = _
    rw [← hh]
    apply integral_congr_ae
    exact .of_forall fun z => mul_comm _ _
  simp only [hn]
  exact (integral_finiteStateGaussianRawKernel_scalar_split R K H c f hfm hi).symm

end FourPapersCommon
