module
public import FourPapersCommon.FiniteCascadeTerminalTranslation
public import FourPapersCommon.FiniteCascadeTreeGaussianRowLaw

@[expose] public section

/-! Literal Gaussian-root formulas for the spin expectation of a recorded
tree. The feature-perturbed numerator is identified with the translated
physical spin genealogy, under its true exponential disorder weight. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy FiniteCascadeGenealogy FRSB
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem integral_finiteCascadeTreeGaussianJointLaw_spins (V : S → ℝ)
    (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (F : Samples S (asGenealogy T) → ℝ) (hF : Measurable F)
    (C : ℝ) (_hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C) :
    (∫z,F (spins T z.2) ∂finiteCascadeTreeGaussianJointLaw V a L s T R H) =
      (∫Q,Real.exp (s*finiteStateGaussianTerminalCascade V a L j Q) *
        (∫σ,F σ ∂finiteCascadeGenealogyKernel V a L (asGenealogy T) Q)
          ∂finiteStateGaussianRawKernel R H) /
            finiteCascadeTreeGaussianNormalizer V a L s j R H := by
  have := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  have := finiteCascadeTreeGaussianJointLaw_probability V a ha L s T R H
  have hsp : Measurable (spins (E:=FiniteStateField S) (S:=S) T) := measurable_spins T
  have hm : Measurable (fun z : FiniteStateField S × Records (FiniteStateField S) S T =>
      F (spins T z.2)) := hF.comp (hsp.comp measurable_snd)
  have hi : Integrable (fun z => F (spins T z.2))
      (finiteCascadeTreeGaussianJointLaw V a L s T R H) :=
    (integrable_const C).mono' hm.aestronglyMeasurable
      (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hFb (spins T z.2))
  rw [finiteCascadeTreeGaussianJointLaw, Measure.integral_compProd hi]
  have he (Q : FiniteStateField S) :
      (∫z,F (spins T z) ∂finiteCascadeTreeRecordKernel V a L T Q) =
        ∫σ,F σ ∂finiteCascadeGenealogyKernel V a L (asGenealogy T) Q := by
    rw [← finiteCascadeTreeRecordKernel_spin_marginal V a ha L T,
      Kernel.map_apply _ (measurable_spins T),
      integral_map (measurable_spins T).aemeasurable hF.aestronglyMeasurable]
  simp_rw [he]
  rw [integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div, integral_div,
    finiteCascadeTreeGaussianNormalizer]

theorem finiteCascadeTreeFeatureNumerator_spins (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s θ : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (F : Samples S (asGenealogy T) → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C) :
    finiteCascadeTreeFeatureNumerator V K a L s T R H (fun z => F (spins T z.2)) θ =
      ∫Q,Real.exp (s*finiteStateGaussianTerminalCascade V a L j (Q+θ • K)) *
        (∫σ,F σ ∂finiteCascadeGenealogyKernel V a L (asGenealogy T) (Q+θ • K))
          ∂finiteStateGaussianRawKernel R H := by
  let W := fun σ => V σ+θ*K σ
  have hz := (finiteCascadeTreeGaussianNormalizer_pos W a ha L s j R H).ne'
  have he := integral_finiteCascadeTreeGaussianFeatureLaw_eq V K a ha L s θ T R H
    (fun z => F (spins T z.2))
  have hj := integral_finiteCascadeTreeGaussianJointLaw_spins W a ha L s T R H F hF C hC hFb
  change (∫z,F (spins T z.2) ∂finiteCascadeTreeGaussianJointLaw W a L s T R H) =
    _ / finiteCascadeTreeGaussianNormalizer W a L s j R H at he
  rw [hj] at he
  have hn := (div_left_inj' hz).mp he.symm
  change finiteCascadeTreeFeatureNumerator V K a L s T R H (fun z => F (spins T z.2)) θ = _ at hn
  rw [hn]
  apply integral_congr_ae
  exact .of_forall fun Q => by
    dsimp only
    rw [show W = fun σ => V σ+(θ • K) σ from rfl,
      finiteStateGaussianTerminalCascade_terminal_add V (θ • K) a L j Q,
      finiteCascadeGenealogyKernel_terminal_add V (θ • K) a ha L (asGenealogy T),
      Kernel.comap_apply]

theorem integral_finiteCascadeTreeGaussianRowLaw_spins (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (hanti : Antitone a) (h0 : a 0 ≤ 1)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s v : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hs : s ≤ finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (B : ℝ) (hB : 0 ≤ B) (hK : ∀σ,|K σ| ≤ B)
    (F : Samples S (asGenealogy T) → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C) :
    (∫z,F (spins T z.2.2) ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H) =
      gaussianHeatFlow (fun θ =>
        ∫Q,Real.exp (s*finiteStateGaussianTerminalCascade V a L j (Q+θ • K)) *
          (∫σ,F σ ∂finiteCascadeGenealogyKernel V a L (asGenealogy T) (Q+θ • K))
            ∂finiteStateGaussianRawKernel R H) v 0 /
              finiteCascadeTreeGaussianRowNormalizer V K a L s v T R H := by
  rw [integral_finiteCascadeTreeGaussianRowLaw_eq V K a ha hanti h0 L s v T hs R H
    B hB hK (fun z => F (spins T z.2))
    (hF.comp ((measurable_spins T).comp measurable_snd)) C hC (fun z => hFb (spins T z.2))]
  congr 2
  funext θ
  exact finiteCascadeTreeFeatureNumerator_spins V K a ha L s θ T R H F hF C hC hFb

end FourPapersCommon
