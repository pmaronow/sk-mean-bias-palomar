module
public import QuantitativePaper.UniformScalarTrialDensity
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! Literal absolute continuity and almost-everywhere ordinary derivative
clauses of the uniform scalar root lemma, from its genuine root Lipschitz
estimate. No two-sided origin differentiability is asserted. -/
noncomputable section
open Set MeasureTheory Paper
open scoped Topology NNReal
namespace QuantitativePaper

theorem scalarEnergyCDF_lipschitzOn (β T C : ℝ) (μ : Paper.ParisiMeasure)
    (hC : 0≤C)
    (hLip : ∀x∈Icc (0:ℝ) T,∀y∈Icc (0:ℝ) T,
      ‖β*parisiCDF μ y-β*parisiCDF μ x‖ ≤ C*‖y-x‖) :
    LipschitzOnWith ⟨C,hC⟩ (fun q=>β*parisiCDF μ q) (Icc (0:ℝ) T) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (β*parisiCDF μ x) (β*parisiCDF μ y) ≤ C*dist x y
  simpa only [Real.dist_eq,Real.norm_eq_abs] using hLip y hy x hx

theorem scalarEnergyCDF_absoluteContinuous (β T C : ℝ) (μ : Paper.ParisiMeasure)
    (hT : 0≤T) (hC : 0≤C)
    (hLip : ∀x∈Icc (0:ℝ) T,∀y∈Icc (0:ℝ) T,
      ‖β*parisiCDF μ y-β*parisiCDF μ x‖ ≤ C*‖y-x‖) :
    AbsolutelyContinuousOnInterval (fun q=>β*parisiCDF μ q) 0 T := by
  have hh:=scalarEnergyCDF_lipschitzOn β T C μ hC hLip
  rw [←uIcc_of_le hT] at hh
  exact hh.absolutelyContinuousOnInterval

theorem scalarEnergyCDF_ae_derivative_bound (β T C : ℝ) (μ : Paper.ParisiMeasure)
    (hβ : 0≤β) (hC : 0≤C)
    (hLip : ∀x∈Icc (0:ℝ) T,∀y∈Icc (0:ℝ) T,
      ‖β*parisiCDF μ y-β*parisiCDF μ x‖ ≤ C*‖y-x‖) :
    ∀ᵐq∂volume.restrict (Icc (0:ℝ) T),
      0≤deriv (fun r=>β*parisiCDF μ r) q ∧
      deriv (fun r=>β*parisiCDF μ r) q≤C := by
  rw [←restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  have hh:=norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hq.1 hq.2)
    (scalarEnergyCDF_lipschitzOn β T C μ hC hLip)
  change ‖deriv (fun r=>β*parisiCDF μ r) q‖ ≤ C at hh
  refine ⟨((parisiCDF_monotone μ).const_mul hβ).deriv_nonneg,?_⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)

end QuantitativePaper
