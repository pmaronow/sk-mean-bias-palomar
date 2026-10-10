module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileFutureValues
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeMeanSquare

@[expose] public section

/-! Genuine restart values at arbitrary initial fields, on one fresh
Wiener space. This transport and its bounded limit do not assume any
initial-field derivative convergence. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128

theorem anisotropicRestartSpinSquare_eq_noise_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (x : Field n) (i : Fin n) :
    anisotropicRestartSpinSquare D μ g q x i r=
      ∫W,(anisotropicRestartNoiseSpinResponse D μ q r i ((g,x),W))^2
        ∂vectorWienerMeasure n := by
  let v : ℝ≥0 := ((r:ℝ)-(q:ℝ)).toNNReal
  have hv : v≤vectorRestartHorizon q := Real.toNNReal_le_toNNReal
    (sub_le_sub_right r.property.2 _)
  have hh : HasLaw (fun p : VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath p.2)
      (vectorWienerMeasure n) (vectorDisorderBrownianMeasure n) :=
    hasLaw_vectorCanonicalBrownianPath.comp (hasLaw_vectorBrownian_samples_with_disorder n)
  have hm : Measurable (fun W=>(anisotropicRestartNoiseSpinResponse D μ q r i ((g,x),W))^2) :=
    (((measurable_uncurry_anisotropicRestartNoiseSpinResponse D μ q i).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).pow_const 2)
  unfold anisotropicRestartSpinSquare
  rw [←hh.map_eq,integral_map hh.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    unfold anisotropicRestartNoiseSpinResponse anisotropicRestartSpinResponse anisotropicRestartPhysicalParameter
    dsimp only
    have he := anisotropicRestartNoiseStatePath_canonical D μ g q
      (anisotropicInverseNoiseMap D x) v hv p
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hqr)] at he
    rw [he]

theorem tendsto_anisotropicRestartNoiseSpinResponse_profile_level
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (g : AnisotropicDisorder n)
    {q r : I→Paper.Overlap} {q₀ r₀ : Paper.Overlap}
    (hq : Tendsto q l (𝓝 q₀)) (hr : Tendsto r l (𝓝 r₀))
    (hqr : ∀j,q j≤r j) (hqr₀ : q₀≤r₀)
    {x : I→Field n} {y : Field n} (hx : Tendsto x l (𝓝 y))
    (i : Fin n) (W : VectorWienerPath n) :
    Tendsto (fun j=>anisotropicRestartNoiseSpinResponse D (μ j) (q j) (r j) i ((g,x j),W)) l
      (𝓝 (anisotropicRestartNoiseSpinResponse D ν q₀ r₀ i ((g,y),W))) := by
  have hx' := (anisotropicInverseNoiseMap D).continuous.tendsto _ |>.comp hx
  have hs := tendsto_anisotropicRestartNoiseStatePath_profile_level D hμ g hq hx' W
    ((continuous_subtype_val.tendsto _ |>.comp hr).sub
      (continuous_subtype_val.tendsto _ |>.comp hq))
    (fun j=>⟨sub_nonneg.mpr (hqr j),sub_le_sub_right (r j).property.2 _⟩)
    ⟨sub_nonneg.mpr hqr₀,sub_le_sub_right r₀.property.2 _⟩
  have hP : Tendsto (fun j=>anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicRestartNoiseStatePath D (μ j) (q j)
        ((g,anisotropicInverseNoiseMap D (x j)),W) ((r j:ℝ)-(q j:ℝ)))) l
      (𝓝 (anisotropicDisorderInjection n g+anisotropicUnitInput D
        (anisotropicRestartNoiseStatePath D ν q₀
          ((g,anisotropicInverseNoiseMap D y),W) ((r₀:ℝ)-(q₀:ℝ))))) :=
    tendsto_const_nhds.add ((anisotropicUnitInput D).continuous.tendsto _ |>.comp hs)
  unfold anisotropicRestartNoiseSpinResponse
  exact (EuclideanSpace.proj i).continuous.tendsto _ |>.comp
    (tendsto_anisotropicMeasureTailMagnetization_profile_time_field D hμ hr hP)

theorem tendsto_anisotropicRestartSpinSquare_profile_level
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (g : AnisotropicDisorder n)
    {q r : I→Paper.Overlap} {q₀ r₀ : Paper.Overlap}
    (hq : Tendsto q l (𝓝 q₀)) (hr : Tendsto r l (𝓝 r₀))
    (hqr : ∀j,q j≤r j) (hqr₀ : q₀≤r₀)
    {x : I→Field n} {y : Field n} (hx : Tendsto x l (𝓝 y)) (i : Fin n) :
    Tendsto (fun j=>anisotropicRestartSpinSquare D (μ j) g (q j) (x j) i (r j)) l
      (𝓝 (anisotropicRestartSpinSquare D ν g q₀ y i r₀)) := by
  simp_rw [anisotropicRestartSpinSquare_eq_noise_integral D _ g _ _ (hqr _),
    anisotropicRestartSpinSquare_eq_noise_integral D ν g q₀ r₀ hqr₀]
  apply tendsto_integral_filter_of_dominated_convergence (fun _=>(1:ℝ))
  · exact .of_forall fun j=>
      (((measurable_uncurry_anisotropicRestartNoiseSpinResponse D (μ j) (q j) i).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).pow_const 2).aestronglyMeasurable
  · exact .of_forall fun j=>.of_forall fun W=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr
        (anisotropicRestartNoiseSpinResponse_bound D (μ j) (q j) (r j) i _)
  · exact integrable_const _
  · exact .of_forall fun W=>
      (tendsto_anisotropicRestartNoiseSpinResponse_profile_level D hμ g hq hr hqr hqr₀ hx i W).pow 2

end QuantitativeFollowup
