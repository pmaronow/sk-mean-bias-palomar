module
public import QuantitativeFollowup.ReflectedCoupling

@[expose] public section

/-! Literal measure, endpoint and CDF-L¹ clauses of reflected global
regularization, with energy normalization. The cost clause requires the
vector first-variation theorem and is kept separate from these proved
measure conclusions. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup

theorem reflected_energy_free_density_le (β : ℝ) (hβ : 0≤β)
    (μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hh : h∈Ioc (0:ℝ) (1/2)) :
    ENNReal.ofReal β • (parisiFreeMeasure (reflectedParisiMeasure μ s h hs hh.1) s).map
      (Subtype.val:Paper.Overlap→ℝ)≤ENNReal.ofReal (β/h) • volume := by
  rw [reflectedParisiMeasure_free μ s h hs hh]
  calc
    _≤ENNReal.ofReal β • (ENNReal.ofReal ((1-s)/h) • volume):=by
      intro S
      change ENNReal.ofReal β*_≤ENNReal.ofReal β*_
      gcongr
      exact reflectedFreeMeasure_density_le μ s h hs hh
    _=ENNReal.ofReal (β*((1-s)/h)) • volume:=by rw [smul_smul,ENNReal.ofReal_mul hβ]
    _ ≤ _ := by
      intro S
      change ENNReal.ofReal (β*((1-s)/h))*volume S≤ENNReal.ofReal (β/h)*volume S
      gcongr
      rw [←mul_div_assoc]
      apply (div_le_div_iff_of_pos_right hh.1).mpr
      nlinarith [mul_nonneg hβ hs.1]

theorem reflected_energy_root (β : ℝ) (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1/2)) :
    β*parisiCDF (reflectedParisiMeasure μ s h hs hh.1) 0=β*s := by
  rw [←zeroMass_eq_parisiCDF_zero,reflectedParisiMeasure_root μ s h hs hh]

theorem reflected_energy_cdfDistance_le (β : ℝ) (hβ : 0≤β)
    (μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor s) (hh : h∈Ioc (0:ℝ) (1/2)) :
    β*parisiCDFDistance μ (reflectedParisiMeasure μ s h hs hh.1)≤β*h := by
  calc
    _≤β*((1-s)*h):=mul_le_mul_of_nonneg_left
      (reflectedParisiMeasure_cdfDistance_le μ s h hs hμ hh) hβ
    _≤β*h:=by nlinarith [mul_nonneg hβ hh.1.le,hs.1]

/-- The actual regularized probability measure realizes the measure-side
conclusions of Lemma 5.2(b), including the exact prescribed root. -/
theorem reflected_regularization_measure_clauses (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (lam h : ℝ) (hlam : lam∈Icc (0:ℝ) β)
    (hμ : μ∈scalarFloor (lam/β)) (hh : h∈Ioc (0:ℝ) (1/2)) :
    ∃ν : Paper.ParisiMeasure,
      β*parisiCDF ν 0=lam ∧ ν∈scalarFloor (lam/β) ∧
      ENNReal.ofReal β • (parisiFreeMeasure ν (lam/β)).map (Subtype.val:Paper.Overlap→ℝ)≤
        ENNReal.ofReal (β/h) • volume ∧
      β*parisiCDFDistance μ ν≤β*h := by
  have hs : lam/β∈Icc (0:ℝ) 1:=⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩
  let ν:=reflectedParisiMeasure μ (lam/β) h hs hh.1
  refine ⟨ν,?_,reflectedParisiMeasure_mem_floor μ (lam/β) h hs hh,
    reflected_energy_free_density_le β hβ.le μ (lam/β) h hs hh,
    reflected_energy_cdfDistance_le β hβ.le μ (lam/β) h hs hμ hh⟩
  rw [reflected_energy_root β μ (lam/β) h hs hh]
  field_simp

end QuantitativeFollowup
