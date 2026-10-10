module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfilePaths
public import QuantitativeFollowup.FollowupCavityRestFutureSquare

@[expose] public section

/-! Actual weak-profile, moving-level continuation values. Every restart
uses the same fresh Wiener driver; the true normalized square is passed
through that fixed probability measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 750000
set_option maxSynthPendingDepth 128

theorem tendsto_anisotropicMeasureTailMagnetization_profile_time_field
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {q : I→Paper.Overlap} {r : Paper.Overlap}
    (hq : Tendsto q l (𝓝 r)) {P : I→AnisotropicParameter n} {Q : AnisotropicParameter n}
    (hP : Tendsto P l (𝓝 Q)) :
    Tendsto (fun j=>anisotropicMeasureTailMagnetization D (μ j) (q j) (P j)) l
      (𝓝 (anisotropicMeasureTailMagnetization D ν r Q)) := by
  have hf := (continuous_anisotropicMeasureTailMagnetization_joint D ν).tendsto _ |>.comp
    (hq.prodMk_nhds hP)
  have he := squeeze_zero (fun j=>norm_nonneg _)
    (fun j=>norm_anisotropicMeasureTailMagnetization_profile_sub_le D (μ j) ν (q j) (P j))
    (tendsto_anisotropicProfileGradientError D μ ν (FRSB.tendsto_parisiCDFDistance_of_tendsto hμ))
  exact tendsto_of_tendsto_of_dist hf (by
    simpa only [dist_eq_norm,norm_sub_rev,Function.comp_def] using he)

theorem tendsto_cavityRestFutureNoiseSpin_profile_level
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {r p : I→Paper.Overlap} {r₀ p₀ : Paper.Overlap}
    (hr : Tendsto r l (𝓝 r₀)) (hp : Tendsto p l (𝓝 p₀))
    (hrp : ∀j,r j≤p j) (hrp₀ : r₀≤p₀) (i : Fin n)
    (ω : AnisotropicDisorderBrownianSample n) (W : VectorWienerPath n) :
    Tendsto (fun j=>cavityRestFutureNoiseSpin D (μ j) (r j) (p j) i ω W) l
      (𝓝 (cavityRestFutureNoiseSpin D ν r₀ p₀ i ω W)) := by
  have hx := (anisotropicInverseNoiseMap D).continuous.tendsto _ |>.comp
    (tendsto_anisotropicMeasureState_profile_time D hμ hr ω)
  have hs := tendsto_anisotropicRestartNoiseStatePath_profile_level D hμ ω.1 hr hx W
    ((continuous_subtype_val.tendsto _ |>.comp hp).sub
      (continuous_subtype_val.tendsto _ |>.comp hr))
    (fun j=>⟨sub_nonneg.mpr (hrp j),sub_le_sub_right (p j).property.2 _⟩)
    ⟨sub_nonneg.mpr hrp₀,sub_le_sub_right p₀.property.2 _⟩
  have he : Tendsto (fun j=>anisotropicExtendedRestartNoiseStatePath D (μ j) ω.1 (r j)
      (anisotropicInverseNoiseMap D (anisotropicMeasureState D (μ j) (r j) ω)) W
      ((p j:ℝ)-(r j:ℝ))) l
      (𝓝 (anisotropicExtendedRestartNoiseStatePath D ν ω.1 r₀
        (anisotropicInverseNoiseMap D (anisotropicMeasureState D ν r₀ ω)) W
        ((p₀:ℝ)-(r₀:ℝ)))) := by
    convert hs using 1
    · funext j
      exact (anisotropicRestartNoiseStatePath_eq_extended D (μ j) ω.1 (r j) _ W _
        ⟨sub_nonneg.mpr (hrp j),sub_le_sub_right (p j).property.2 _⟩).symm
    · congr 1
      exact (anisotropicRestartNoiseStatePath_eq_extended D ν ω.1 r₀ _ W _
        ⟨sub_nonneg.mpr hrp₀,sub_le_sub_right p₀.property.2 _⟩).symm
  have hP : Tendsto (fun j=>anisotropicDisorderInjection n ω.1+anisotropicUnitInput D
      (anisotropicExtendedRestartNoiseStatePath D (μ j) ω.1 (r j)
        (anisotropicInverseNoiseMap D (anisotropicMeasureState D (μ j) (r j) ω)) W
        ((p j:ℝ)-(r j:ℝ)))) l
      (𝓝 (anisotropicDisorderInjection n ω.1+anisotropicUnitInput D
        (anisotropicExtendedRestartNoiseStatePath D ν ω.1 r₀
          (anisotropicInverseNoiseMap D (anisotropicMeasureState D ν r₀ ω)) W
          ((p₀:ℝ)-(r₀:ℝ))))) :=
    tendsto_const_nhds.add ((anisotropicUnitInput D).continuous.tendsto _ |>.comp he)
  unfold cavityRestFutureNoiseSpin
  exact (EuclideanSpace.proj i).continuous.tendsto _ |>.comp
    (tendsto_anisotropicMeasureTailMagnetization_profile_time_field D hμ hp hP)

theorem tendsto_cavityRestFutureSquare_profile_level
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {r p : I→Paper.Overlap} {r₀ p₀ : Paper.Overlap}
    (hr : Tendsto r l (𝓝 r₀)) (hp : Tendsto p l (𝓝 p₀))
    (hrp : ∀j,r j≤p j) (hrp₀ : r₀≤p₀)
    (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j=>cavityRestFutureSquare D (μ j) (r j) (p j) ω) l
      (𝓝 (cavityRestFutureSquare D ν r₀ p₀ ω)) := by
  unfold cavityRestFutureSquare
  apply Tendsto.div_const
  apply tendsto_finsetSum
  intro i _
  apply tendsto_integral_filter_of_dominated_convergence (fun _=>(1:ℝ))
  · exact .of_forall fun j=>by
      have hm : Measurable (fun W : VectorWienerPath n=>((r j,p j,ω),W)) :=
        measurable_const.prodMk measurable_id
      exact (((measurable_cavityRestFutureNoiseSpin D (μ j) i).comp hm).pow_const 2).aestronglyMeasurable
  · exact .of_forall fun j=>.of_forall fun W=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr
        (anisotropicMeasureTailMagnetization_component_bound D (μ j) (p j) _ i)
  · exact integrable_const _
  · exact .of_forall fun W=>
      (tendsto_cavityRestFutureNoiseSpin_profile_level D hμ hr hp hrp hrp₀ i ω W).pow 2

end QuantitativeFollowup
