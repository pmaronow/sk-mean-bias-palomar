module
public import FourPapersCommon.FiniteCascadeRecordTranslation
public import FourPapersCommon.FiniteCascadeGaussianSpinIntegral

@[expose] public section

/-! Gaussian-root formulas retain every genuine field record. Terminal
translations therefore identify arbitrary bounded record observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem measurable_finiteCascadeShiftRecords_joint (K : FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (fun z : ℝ × Records (FiniteStateField S) S T =>
      finiteCascadeShiftRecords K z.1 T z.2) := by
  induction T with
  | leaf => exact measurable_snd
  | advance T ih =>
      change Measurable (fun z : ℝ × (FiniteStateField S × Records (FiniteStateField S) S T) => (z.2.1 + z.1 • K,
        finiteCascadeShiftRecords K z.1 T z.2.2))
      exact ((measurable_fst.comp measurable_snd).add
        (measurable_fst.smul_const K)).prodMk
        (ih.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  | fork T U ihT ihU =>
      exact (ihT.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
        (ihU.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

theorem integral_finiteCascadeTreeGaussianJointLaw_records (V : S → ℝ)
    (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S × Records (FiniteStateField S) S T → ℝ)
    (hF : Measurable F) (C : ℝ) (hFb : ∀z,|F z| ≤ C) :
    (∫z,F z ∂finiteCascadeTreeGaussianJointLaw V a L s T R H) =
      (∫Q,Real.exp (s*finiteStateGaussianTerminalCascade V a L j Q) *
        (∫z,F (Q,z) ∂finiteCascadeTreeRecordKernel V a L T Q)
          ∂finiteStateGaussianRawKernel R H) /
            finiteCascadeTreeGaussianNormalizer V a L s j R H := by
  have := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  have := finiteCascadeTreeGaussianJointLaw_probability V a ha L s T R H
  have hi : Integrable F (finiteCascadeTreeGaussianJointLaw V a L s T R H) :=
    (integrable_const C).mono' hF.aestronglyMeasurable
      (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hFb z)
  rw [finiteCascadeTreeGaussianJointLaw, Measure.integral_compProd hi, integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div, integral_div,
    finiteCascadeTreeGaussianNormalizer]

theorem finiteCascadeTreeFeatureNumerator_records (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s θ : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S × Records (FiniteStateField S) S T → ℝ)
    (hF : Measurable F) (C : ℝ) (hFb : ∀z,|F z| ≤ C) :
    finiteCascadeTreeFeatureNumerator V K a L s T R H
      (fun z => F (z.1+θ • K,finiteCascadeShiftRecords K θ T z.2)) θ =
      ∫Q,Real.exp (s*finiteStateGaussianTerminalCascade V a L j (Q+θ • K)) *
        (∫z,F (Q+θ • K,z) ∂finiteCascadeTreeRecordKernel V a L T (Q+θ • K))
          ∂finiteStateGaussianRawKernel R H := by
  let W := fun σ => V σ+θ*K σ
  let G := fun z : FiniteStateField S × Records (FiniteStateField S) S T =>
    F (z.1+θ • K,finiteCascadeShiftRecords K θ T z.2)
  have hG : Measurable G := hF.comp
    ((measurable_fst.add_const _).prodMk
      ((measurable_finiteCascadeShiftRecords K θ T).comp measurable_snd))
  have he := integral_finiteCascadeTreeGaussianFeatureLaw_eq V K a ha L s θ T R H G
  have hj := integral_finiteCascadeTreeGaussianJointLaw_records W a ha L s T R H G hG C
    (fun z => hFb _)
  change (∫z,G z ∂finiteCascadeTreeGaussianJointLaw W a L s T R H) =
    _ / finiteCascadeTreeGaussianNormalizer W a L s j R H at he
  rw [hj] at he
  have hn := (div_left_inj' (finiteCascadeTreeGaussianNormalizer_pos W a ha L s j R H).ne').mp he.symm
  change finiteCascadeTreeFeatureNumerator V K a L s T R H G θ = _ at hn
  change finiteCascadeTreeFeatureNumerator V K a L s T R H G θ = _
  rw [hn]
  apply integral_congr_ae
  exact .of_forall fun Q => by
    dsimp only [W,G]
    rw [show (fun σ => V σ+θ*K σ) = (fun σ => V σ+(θ • K) σ) from rfl,
      finiteStateGaussianTerminalCascade_terminal_add V (θ • K)]
    congr 1
    have hes : finiteCascadeShiftRecords K θ T = finiteCascadeShiftRecords (θ • K) 1 T := by
      funext z
      exact (finiteCascadeShiftRecords_smul K θ T z).symm
    simp only [hes]
    have hmap := integral_map (μ := finiteCascadeTreeRecordKernel
      (fun σ => V σ+(θ • K) σ) a L T Q)
      (measurable_finiteCascadeShiftRecords (θ • K) 1 T).aemeasurable
      (show AEStronglyMeasurable (fun z : Records (FiniteStateField S) S T =>
        F (Q+θ • K,z)) ((finiteCascadeTreeRecordKernel
          (fun σ => V σ+(θ • K) σ) a L T Q).map
            (finiteCascadeShiftRecords (θ • K) 1 T)) from
        (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    simp only [Function.comp_def] at hmap
    rw [← hmap, ← Kernel.map_apply _ (measurable_finiteCascadeShiftRecords (θ • K) 1 T),
      finiteCascadeTreeRecordKernel_terminal_add V (θ • K) a ha L T, Kernel.comap_apply]

end FourPapersCommon
