module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileRestartValues
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeLipschitz

@[expose] public section

/-! Genuine weak-profile restart derivatives. Actual value convergence and
the inherited uniform field moduli give locally uniform derivative limits;
uniqueness identifies those limits with the native initial-field derivative. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 128

theorem tendstoLocallyUniformly_anisotropicRestartSpinSquare_field_derivative_profile
    (D : AnisotropicSpinModel n) {μ : ℕ→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ atTop (𝓝 ν)) (g : AnisotropicDisorder n)
    {q r : ℕ→Paper.Overlap} {q₀ r₀ : Paper.Overlap}
    (hq : Tendsto q atTop (𝓝 q₀)) (hr : Tendsto r atTop (𝓝 r₀))
    (hqr : ∀j,q j≤r j) (hqr₀ : q₀≤r₀) (i : Fin n) :
    TendstoLocallyUniformly
      (fun j=>fderiv ℝ (fun x=>anisotropicRestartSpinSquare D (μ j) g (q j) x i (r j)))
      (fderiv ℝ (fun x=>anisotropicRestartSpinSquare D ν g q₀ x i r₀)) atTop := by
  obtain ⟨G',hu,hd,_,_⟩ := exists_local_derivative_limit_of_pointwise
    (fun j x=>anisotropicRestartSpinSquare D (μ j) g (q j) x i (r j))
    (fun x=>anisotropicRestartSpinSquare D ν g q₀ x i r₀)
    (fun j=>(contDiff_anisotropicRestartSpinSquare_field D (μ j) g (q j) (r j) (hqr j) i).differentiable_one)
    (4*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊)
    (31*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊^2)
    (fun j=>anisotropicRestartSpinSquare_field_lipschitz D (μ j) g (q j) (r j) (hqr j) i)
    (fun j=>anisotropicRestartSpinSquare_field_differential_lipschitz D (μ j) g (q j) (r j) (hqr j) i)
    (fun x=>tendsto_anisotropicRestartSpinSquare_profile_level D hμ g hq hr hqr hqr₀ tendsto_const_nhds i)
  have he : G'=fderiv ℝ (fun x=>anisotropicRestartSpinSquare D ν g q₀ x i r₀) :=
    funext fun x=>(hd x).fderiv.symm
  rwa [he] at hu

theorem tendsto_anisotropicRestartSpinSquare_field_derivative_profile_moving
    (D : AnisotropicSpinModel n) {μ : ℕ→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ atTop (𝓝 ν)) (g : AnisotropicDisorder n)
    {q r : ℕ→Paper.Overlap} {q₀ r₀ : Paper.Overlap}
    (hq : Tendsto q atTop (𝓝 q₀)) (hr : Tendsto r atTop (𝓝 r₀))
    (hqr : ∀j,q j≤r j) (hqr₀ : q₀≤r₀) {x : ℕ→Field n} {y : Field n}
    (hx : Tendsto x atTop (𝓝 y)) (i : Fin n) :
    Tendsto (fun j=>fderiv ℝ (fun z=>anisotropicRestartSpinSquare D (μ j) g (q j) z i (r j)) (x j))
      atTop (𝓝 (fderiv ℝ (fun z=>anisotropicRestartSpinSquare D ν g q₀ z i r₀) y)) := by
  have hu := tendstoLocallyUniformlyOn_univ.mpr
    (tendstoLocallyUniformly_anisotropicRestartSpinSquare_field_derivative_profile D hμ g hq hr hqr hqr₀ i)
  have hf := hu.tendsto_at (mem_univ y)
  let K : ℝ≥0 := 31*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊^2
  have hdx : Tendsto (fun j=>(K:ℝ)*dist (x j) y) atTop (𝓝 0) := by
    simpa only [dist_self,mul_zero] using (hx.dist (tendsto_const_nhds (x:=y))).const_mul (K:ℝ)
  have he := squeeze_zero (fun j=>dist_nonneg) (fun j=>
    (anisotropicRestartSpinSquare_field_differential_lipschitz D (μ j) g (q j) (r j) (hqr j) i).dist_le_mul (x j) y)
    hdx
  exact tendsto_of_tendsto_of_dist hf (by simpa only [dist_comm,Function.comp_def] using he)

theorem fderiv_anisotropicRestartMeanSquare_field_sum (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (x : Field n) :
    fderiv ℝ (fun y=>anisotropicRestartMeanSquare D μ g q y r) x=
      ((n:ℝ)⁻¹) •∑i : Fin n,fderiv ℝ (fun y=>anisotropicRestartSpinSquare D μ g q y i r) x := by
  have hd (i : Fin n) := (contDiff_anisotropicRestartSpinSquare_field D μ g q r hqr i).differentiable_one x
  have hs := HasFDerivAt.fun_sum (u:=Finset.univ) (fun i _=>(hd i).hasFDerivAt)
  simpa only [anisotropicRestartMeanSquare,div_eq_mul_inv,mul_comm] using
    (hs.const_mul ((n:ℝ)⁻¹)).fderiv

theorem tendsto_anisotropicRestartMeanSquare_field_derivative_profile_moving
    (D : AnisotropicSpinModel n) {μ : ℕ→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ atTop (𝓝 ν)) (g : AnisotropicDisorder n)
    {q r : ℕ→Paper.Overlap} {q₀ r₀ : Paper.Overlap}
    (hq : Tendsto q atTop (𝓝 q₀)) (hr : Tendsto r atTop (𝓝 r₀))
    (hqr : ∀j,q j≤r j) (hqr₀ : q₀≤r₀) {x : ℕ→Field n} {y : Field n}
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun j=>fderiv ℝ (fun z=>anisotropicRestartMeanSquare D (μ j) g (q j) z (r j)) (x j))
      atTop (𝓝 (fderiv ℝ (fun z=>anisotropicRestartMeanSquare D ν g q₀ z r₀) y)) := by
  simp_rw [fderiv_anisotropicRestartMeanSquare_field_sum D _ g _ _ (hqr _),
    fderiv_anisotropicRestartMeanSquare_field_sum D ν g q₀ r₀ hqr₀]
  apply Tendsto.const_smul
  exact tendsto_finsetSum Finset.univ fun i _=>
    tendsto_anisotropicRestartSpinSquare_field_derivative_profile_moving D hμ g hq hr hqr hqr₀ hx i

end QuantitativeFollowup
