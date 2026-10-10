module
public import QuantitativeFollowup.PartialReflectedPotentialCost

@[expose] public section

/-! All partial reflected regularization clauses, including the literal
energy cost with the actual free mass below the cutoff. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem partial_reflected_followup_energy_cost_le (n : ℕ) (hn : 0<n)
    (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure) (lam rho T h : ℝ)
    (hlam : lam∈Icc (0:ℝ) β) (hrho : rho∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor (lam/β)) (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T)) :
    followupEnergyFunctional n β lam rho
      (partialReflectedParisiMeasure μ (lam/β) T h
        ⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩ hh.1)-
      followupEnergyFunctional n β lam rho μ≤
      rho*(β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow T))*h^2/12 := by
  have hs:lam/β∈Icc (0:ℝ) 1:=⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩
  have hh0:=partial_reflected_vector_functional_cost_le hn μ (lam/β) T h hs hμ hT hh β (1-rho) (lam/β)
    hβ.ne' (by linarith [hrho.1]) (div_nonneg hlam.1 hβ.le)
  have hd:=div_le_div_of_nonneg_right hh0 hβ.le
  unfold followupEnergyFunctional
  rw [←sub_div]
  convert hd using 1
  field_simp
  ring

/-- Lemma 5.2(a), with an actual measure and all literal root, floor,
absolute-continuity and energy-cost conclusions. -/
theorem partial_reflected_regularization_full (n : ℕ) (hn : 0<n)
    (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure) (lam rho T h : ℝ)
    (hlam : lam∈Icc (0:ℝ) β) (hrho : rho∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor (lam/β)) (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T)) :
    ∃ν : Paper.ParisiMeasure,
      β*parisiCDF ν 0=lam ∧ ν∈scalarFloor (lam/β) ∧
      (ENNReal.ofReal β • (parisiFreeMeasure ν (lam/β)).map
        (Subtype.val:Paper.Overlap→ℝ)).restrict (Iio T)≤
        ENNReal.ofReal (β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow T)/h) • volume.restrict (Iio T) ∧
      followupEnergyFunctional n β lam rho ν-followupEnergyFunctional n β lam rho μ≤
        rho*(β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow T))*h^2/12 := by
  have hs:lam/β∈Icc (0:ℝ) 1:=⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩
  let ν:=partialReflectedParisiMeasure μ (lam/β) T h hs hh.1
  refine ⟨ν,?_,?_,partial_reflected_energy_density_le β hβ.le μ (lam/β) T h hs hT hh,
    partial_reflected_followup_energy_cost_le n hn β hβ μ lam rho T h hlam hrho hμ hT hh⟩
  · rw [partial_reflected_energy_root β μ (lam/β) T h hs hT hh]
    field_simp
  · rw [mem_scalarFloor_iff,partialReflectedParisiMeasure_root μ (lam/β) T h hs hT hh]

end QuantitativeFollowup
