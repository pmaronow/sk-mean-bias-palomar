module
public import QuantitativeFollowup.PartialReflectedMeasure

@[expose] public section

/-! The exact energy-normalized measure clauses of Lemma 5.2(a).
The mass factor is the actual free mass strictly below T, including its
possible atom at zero and excluding its possible atom at T. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup

theorem partial_reflected_energy_density_le (β : ℝ) (hβ : 0≤β)
    (μ : Paper.ParisiMeasure) (s T h : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T)) :
    (ENNReal.ofReal β • (parisiFreeMeasure (partialReflectedParisiMeasure μ s T h hs hh.1) s).map
      (Subtype.val:Paper.Overlap→ℝ)).restrict (Iio T)≤
      ENNReal.ofReal (β*(parisiFreeMeasure μ s).real (overlapBelow T)/h) • volume.restrict (Iio T) := by
  rw [partialReflectedParisiMeasure_free μ s T h hs hT hh,Measure.restrict_smul]
  calc
    _≤ENNReal.ofReal β • ((ENNReal.ofReal (1/h)*(parisiFreeMeasure μ s (overlapBelow T))) •
        volume.restrict (Iio T)):=by
      intro S
      change ENNReal.ofReal β*_≤ENNReal.ofReal β*_
      gcongr
      exact partialReflectedFreeMeasure_density_below μ s T h hT hh
    _=_:=by
      rw [smul_smul,←ENNReal.ofReal_toReal (measure_ne_top (parisiFreeMeasure μ s) (overlapBelow T)),
        ←ENNReal.ofReal_mul (by exact one_div_nonneg.mpr hh.1.le),←ENNReal.ofReal_mul hβ]
      congr 2
      change β*(1/h*(parisiFreeMeasure μ s (overlapBelow T)).toReal)=
        β*(parisiFreeMeasure μ s (overlapBelow T)).toReal/h
      ring

theorem partial_reflected_energy_root (β : ℝ) (μ : Paper.ParisiMeasure) (s T h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T)) :
    β*parisiCDF (partialReflectedParisiMeasure μ s T h hs hh.1) 0=β*s := by
  rw [←zeroMass_eq_parisiCDF_zero,partialReflectedParisiMeasure_root μ s T h hs hT hh]

theorem partial_reflected_regularization_measure_clauses (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (lam T h : ℝ) (hlam : lam∈Icc (0:ℝ) β)
    (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T)) :
    ∃ν : Paper.ParisiMeasure,
      β*parisiCDF ν 0=lam ∧ ν∈scalarFloor (lam/β) ∧
      (ENNReal.ofReal β • (parisiFreeMeasure ν (lam/β)).map (Subtype.val:Paper.Overlap→ℝ)).restrict (Iio T)≤
        ENNReal.ofReal (β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow T)/h) • volume.restrict (Iio T) := by
  have hs : lam/β∈Icc (0:ℝ) 1:=⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩
  let ν:=partialReflectedParisiMeasure μ (lam/β) T h hs hh.1
  refine ⟨ν,?_,?_,partial_reflected_energy_density_le β hβ.le μ (lam/β) T h hs hT hh⟩
  · rw [partial_reflected_energy_root β μ (lam/β) T h hs hT hh]
    field_simp
  · rw [mem_scalarFloor_iff,partialReflectedParisiMeasure_root μ (lam/β) T h hs hT hh]

end QuantitativeFollowup
