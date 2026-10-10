module
public import FourPapersCommon.ParisiGridMix
public import QuantitativePaper.VectorProfileRecursion

@[expose] public section

/-! Literal affine finite profiles on a common grid are the grid scheme of
the actual probability-measure mixture. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1200000

theorem rsbScheme_ext {k : ℕ} (s r : RSBScheme k) (hm : s.m = r.m) (hq : s.q = r.q) : s = r := by
  cases s
  cases r
  simp_all

theorem parisiGridSchemeMass_mix (μ ν : Paper.ParisiMeasure) (N : ℕ) (θ : ℝ)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (i : ℕ) :
    Paper.parisiGridSchemeMass (Paper.parisiMix μ ν θ) N i =
      (1-θ)*Paper.parisiGridSchemeMass μ N i + θ*Paper.parisiGridSchemeMass ν N i := by
  unfold Paper.parisiGridSchemeMass
  by_cases hi : i = 0
  · simp only [hi, ite_true, mul_zero, add_zero]
  · simp only [hi, ite_false]
    rw [parisiGridMeasure_mix μ ν N θ hθ, Paper.parisiCDF_mix _ _ θ _ hθ]

theorem vector_grid_profile_scheme_eq_mix (μ ν : Paper.ParisiMeasure) (N : ℕ) (θ : ℝ)
    (hθ : θ ∈ Icc (0 : ℝ) 1) :
    vectorProfileScheme (Paper.parisiGridRSBScheme μ N) (Paper.parisiGridRSBScheme ν N) θ hθ =
      Paper.parisiGridRSBScheme (Paper.parisiMix μ ν θ) N := by
  apply rsbScheme_ext
  · funext i
    exact (parisiGridSchemeMass_mix μ ν N θ hθ i).symm
  · rfl

end QuantitativePaper
