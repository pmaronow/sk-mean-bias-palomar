module
public import QuantitativePaper.VectorSharpProfileStability
public import QuantitativePaper.VectorProfileSchemeMix
public import QuantitativePaper.VectorProfileInteriorSmooth
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-! Depth-independent first profile bounds for the actual affine Parisi
profile. The arbitrary-measure assertion is Lipschitz continuity; genuine
finite derivatives are identified separately by the actual smooth recursion.
No arbitrary-measure second differentiability is asserted here. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1200000

theorem vectorTailCDFDistance_mix_exact (μ ν : Paper.ParisiMeasure)
    (θ φ q : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) (hφ : φ ∈ Icc (0:ℝ) 1) :
    vectorTailCDFDistance (Paper.parisiMix μ ν θ) (Paper.parisiMix μ ν φ) q =
      |θ-φ| *vectorTailCDFDistance μ ν q := by
  unfold vectorTailCDFDistance
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro a _
  dsimp only
  rw [Paper.parisiCDF_mix μ ν θ a hθ, Paper.parisiCDF_mix μ ν φ a hφ]
  have he : (1-θ)*Paper.parisiCDF μ a+θ*Paper.parisiCDF ν a-
      ((1-φ)*Paper.parisiCDF μ a+φ*Paper.parisiCDF ν a) =
      (θ-φ)*(Paper.parisiCDF ν a-Paper.parisiCDF μ a) := by ring
  rw [he,abs_mul,abs_sub_comm (Paper.parisiCDF ν a)]

theorem vectorTailCDFDistance_le_tail_length (μ ν : Paper.ParisiMeasure)
    (q : ℝ) (hq : q ≤ 1) : vectorTailCDFDistance μ ν q ≤ 1-q := by
  have hh := intervalIntegral.integral_mono_on hq
    (Paper.parisiCDF_abs_diff_intervalIntegrable μ ν q 1)
    (intervalIntegrable_const (c:=(1:ℝ))) (fun a _ => by
      rw [abs_le]
      constructor <;> linarith [Paper.parisiCDF_nonneg μ a,
        Paper.parisiCDF_nonneg ν a,Paper.parisiCDF_le_one μ a,Paper.parisiCDF_le_one ν a])
  simpa only [vectorTailCDFDistance,intervalIntegral.integral_const,smul_eq_mul,mul_one]
    using hh

theorem vectorMeasureTailPotential_mix_lipschitzOn {n : ℕ}
    (μ ν : Paper.ParisiMeasure) (β t q : ℝ) (ht : t ≤ 1)
    (hq : q ∈ Icc (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    LipschitzOnWith ((n:ℝ)*((1-t)*β^2)/2*(1-q)).toNNReal
      (fun θ => vectorMeasureTailPotential (Paper.parisiMix μ ν θ) β t q p x)
      (Icc (0:ℝ) 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro θ hθ φ hφ
  have hcoef : 0 ≤ (n:ℝ)*((1-t)*β^2)/2 := by positivity
  have hbound := vectorMeasureTailPotential_tail_distance_abs_sub_le_half
    (Paper.parisiMix μ ν θ) (Paper.parisiMix μ ν φ) β t q ht hq p x
  rw [vectorTailCDFDistance_mix_exact μ ν θ φ q hθ hφ] at hbound
  have hlength := mul_le_mul_of_nonneg_left
    (vectorTailCDFDistance_le_tail_length μ ν q hq.2) (abs_nonneg (θ-φ))
  rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ (mul_nonneg hcoef (sub_nonneg.mpr hq.2))]
  calc
    _ ≤ (n:ℝ)*((1-t)*β^2)/2*(|θ-φ| *vectorTailCDFDistance μ ν q) := hbound
    _ ≤ (n:ℝ)*((1-t)*β^2)/2*(|θ-φ| *(1-q)) :=
      mul_le_mul_of_nonneg_left hlength hcoef
    _ = _ := by ring

theorem vectorProfileTailRecursion_lipschitzOn_profile {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (hgrid : ∀ i, i ≤ k+2 → s₀.q i=s₁.q i)
    (β t q : ℝ) (ht : t ≤ 1) (hq : q ∈ Icc (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    LipschitzOnWith ((n:ℝ)*((1-t)*β^2)/2*(1-q)).toNNReal
      (fun θ => vectorProfileTailRecursion s₀ s₁ β t q θ p (k+2) x)
      (Icc (0:ℝ) 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro θ hθ φ hφ
  have hcoef : 0 ≤ (n:ℝ)*((1-t)*β^2)/2 := by positivity
  have hbound := vectorTailRecursion_aligned_tail_distance_abs_sub_le_half
    (vectorProfileScheme s₀ s₁ θ hθ) (vectorProfileScheme s₀ s₁ φ hφ) β t q ht hq
    (fun _ _ => rfl) p x
  rw [vectorProfileSchemeMeasure_mix s₀ s₁ hgrid θ hθ,
    vectorProfileSchemeMeasure_mix s₀ s₁ hgrid φ hφ,
    vectorTailCDFDistance_mix_exact _ _ θ φ q hθ hφ] at hbound
  have hlength := mul_le_mul_of_nonneg_left
    (vectorTailCDFDistance_le_tail_length (Paper.parisiSchemeMeasure s₀)
      (Paper.parisiSchemeMeasure s₁) q hq.2) (abs_nonneg (θ-φ))
  rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ (mul_nonneg hcoef (sub_nonneg.mpr hq.2)),
    vectorProfileTailRecursion_eq_scheme s₀ s₁ β t q θ hθ,
    vectorProfileTailRecursion_eq_scheme s₀ s₁ β t q φ hφ]
  calc
    _ ≤ (n:ℝ)*((1-t)*β^2)/2*
        (|θ-φ| *vectorTailCDFDistance (Paper.parisiSchemeMeasure s₀) (Paper.parisiSchemeMeasure s₁) q) :=
      hbound
    _ ≤ (n:ℝ)*((1-t)*β^2)/2*(|θ-φ| *(1-q)) :=
      mul_le_mul_of_nonneg_left hlength hcoef
    _ = _ := by ring

theorem vectorProfileTailRecursion_hasDerivAt_profile {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t q θ : ℝ) (ht : t ≤ 1)
    (hq : q ∈ Icc (0:ℝ) 1) (hθ : θ ∈ Ioo (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    HasDerivAt (fun φ => vectorProfileTailRecursion s₀ s₁ β t q φ p (k+2) x)
      (deriv (fun φ => vectorProfileTailRecursion s₀ s₁ β t q φ p (k+2) x) θ) θ := by
  have hs := contDiffAt_vectorProfileTailRecursion_joint s₀ s₁ β t q ht hq
    (k+2) le_rfl (θ,(p,x)) hθ
  have hc : ContDiffAt ℝ ∞ (fun φ : ℝ => (φ,(p,x))) θ :=
    contDiffAt_id.prodMk contDiffAt_const
  exact ((hs.comp θ hc).differentiableAt (by simp)).hasDerivAt

theorem norm_vectorProfileTailRecursion_profile_deriv_le {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (hgrid : ∀ i, i ≤ k+2 → s₀.q i=s₁.q i)
    (β t q θ : ℝ) (ht : t ≤ 1) (hq : q ∈ Icc (0:ℝ) 1)
    (hθ : θ ∈ Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    ‖deriv (fun φ => vectorProfileTailRecursion s₀ s₁ β t q φ p (k+2) x) θ‖ ≤
      (n:ℝ)*((1-t)*β^2)/2*(1-q) := by
  have hh := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hθ.1 hθ.2)
    (vectorProfileTailRecursion_lipschitzOn_profile s₀ s₁ hgrid β t q ht hq p x)
  have hC : 0 ≤ (n:ℝ)*((1-t)*β^2)/2*(1-q) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hq.2)
  simpa only [Real.coe_toNNReal _ hC] using hh

end QuantitativePaper
