module
public import QuantitativeFollowup.ReflectedPotentialCost
public import QuantitativeFollowup.ReflectedRegularization

@[expose] public section

/-! Literal global reflected regularization for the actual energy-scaled
finite-system Parisi functional, including the zero-noise endpoint. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

/-- The follow-up's actual energy normalization and physical clock. -/
def followupEnergyFunctional (n : ℕ) (β lam rho : ℝ) (μ : Paper.ParisiMeasure) : ℝ :=
  vectorMeasureFunctional n μ β (1-rho) (lam/β)/β

theorem reflected_vector_functional_cost_le_closed {n : ℕ} (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor s) (hh : h∈Ioc (0:ℝ) (1/2))
    (β t a : ℝ) (hβ : β≠0) (ht : t≤1) (ha : 0≤a) :
    vectorMeasureFunctional n (reflectedParisiMeasure μ s h hs hh.1) β t a-
      vectorMeasureFunctional n μ β t a≤((1-t)*β^2)*(1-s)*h^2/12 := by
  by_cases ht1:t=1
  · subst t
    simp only [vectorMeasureFunctional,sub_self,zero_mul,sub_zero]
    simp_rw [vectorMeasurePotential_one_zero]
    simp
  · exact reflected_vector_functional_cost_le hn μ s h hs hμ hh β t a hβ (lt_of_le_of_ne ht ht1) ha

theorem reflected_followup_energy_cost_le (n : ℕ) (hn : 0<n)
    (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure) (lam rho h : ℝ)
    (hlam : lam∈Icc (0:ℝ) β) (hrho : rho∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor (lam/β)) (hh : h∈Ioc (0:ℝ) (1/2)) :
    followupEnergyFunctional n β lam rho
      (reflectedParisiMeasure μ (lam/β) h
        ⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩ hh.1)-
      followupEnergyFunctional n β lam rho μ≤rho*(β-lam)*h^2/12 := by
  have hs:lam/β∈Icc (0:ℝ) 1:=⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩
  have hh0:=reflected_vector_functional_cost_le_closed hn μ (lam/β) h hs hμ hh β (1-rho) (lam/β)
    hβ.ne' (by linarith [hrho.1]) (div_nonneg hlam.1 hβ.le)
  have hd:=div_le_div_of_nonneg_right hh0 hβ.le
  unfold followupEnergyFunctional
  rw [←sub_div]
  convert hd using 1
  field_simp
  ring

/-- Every admissible profile has a genuine reflected trial profile with
all of Lemma 5.2(b)'s density, endpoint, transport and actual cost bounds. -/
theorem reflected_regularization_full (n : ℕ) (hn : 0<n)
    (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure) (lam rho h : ℝ)
    (hlam : lam∈Icc (0:ℝ) β) (hrho : rho∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor (lam/β)) (hh : h∈Ioc (0:ℝ) (1/2)) :
    ∃ν : Paper.ParisiMeasure,
      β*parisiCDF ν 0=lam ∧ ν∈scalarFloor (lam/β) ∧
      ENNReal.ofReal β • (parisiFreeMeasure ν (lam/β)).map (Subtype.val:Paper.Overlap→ℝ)≤
        ENNReal.ofReal (β/h) • volume ∧ β*parisiCDFDistance μ ν≤β*h ∧
      followupEnergyFunctional n β lam rho ν-followupEnergyFunctional n β lam rho μ≤rho*β*h^2/12 := by
  have hs:lam/β∈Icc (0:ℝ) 1:=⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩
  let ν:=reflectedParisiMeasure μ (lam/β) h hs hh.1
  refine ⟨ν,?_,reflectedParisiMeasure_mem_floor μ (lam/β) h hs hh,
    reflected_energy_free_density_le β hβ.le μ (lam/β) h hs hh,
    reflected_energy_cdfDistance_le β hβ.le μ (lam/β) h hs hμ hh,?_⟩
  · rw [reflected_energy_root β μ (lam/β) h hs hh]
    field_simp
  · have hc:=reflected_followup_energy_cost_le n hn β hβ μ lam rho h hlam hrho hμ hh
    change followupEnergyFunctional n β lam rho ν-followupEnergyFunctional n β lam rho μ≤_ at hc ⊢
    apply hc.trans
    nlinarith [mul_nonneg (mul_nonneg hrho.1 hlam.1) (sq_nonneg h)]

end QuantitativeFollowup
