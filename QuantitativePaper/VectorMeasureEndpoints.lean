module
public import QuantitativePaper.VectorMeasurePotential

@[expose] public section

/-! The constructed arbitrary-profile potential has the genuine physical
SK and scalar Parisi endpoints. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

theorem tendsto_vectorDyadicIndex : Tendsto vectorDyadicIndex atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hp : Tendsto (fun j : ℕ => (2 : ℕ)^j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega : 1<(2 : ℕ))
  filter_upwards [hp.eventually (eventually_ge_atTop (b+1))] with j hj
  unfold vectorDyadicIndex
  omega

theorem vectorMeasurePotential_zero {n : ℕ} (μ : Paper.ParisiMeasure) (β : ℝ) (hβ : β≠0)
    (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasurePotential μ β 0 p x=∑i : Fin n,(Real.log 2+Paper.parisiPotential β μ (0,x i)) := by
  have hlim : Tendsto (fun j : ℕ => ∑i : Fin n,
      (Real.log 2+Paper.parisiFinitePotential (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β (0,x i)))
      atTop (𝓝 (∑i : Fin n,(Real.log 2+Paper.parisiPotential β μ (0,x i)))) := by
    apply tendsto_finsetSum
    intro i hi
    exact tendsto_const_nhds.add
      ((Paper.tendsto_actual_finiteParisiPotential β hβ μ 0 (x i) ⟨le_rfl,by norm_num⟩).comp
        tendsto_vectorDyadicIndex)
  have he : (fun j => vectorDyadicPotential μ β 0 j p x)=
      (fun j : ℕ => ∑i : Fin n,
        (Real.log 2+Paper.parisiFinitePotential (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β (0,x i))) := by
    funext j
    unfold vectorDyadicPotential
    rw [vectorRecursion_zero_time]
    simp only [Paper.parisiFinitePotential_initial]
  rw [←he] at hlim
  exact tendsto_nhds_unique (tendsto_vectorDyadicPotential μ β 0 (by norm_num) p x) hlim

theorem vectorMeasurePotential_one_zero (n : ℕ) (μ : Paper.ParisiMeasure) (β : ℝ)
    (p : Couplings n×ℝ) :
    vectorMeasurePotential μ β 1 p 0=completedLogPartition n β p := by
  rw [vectorMeasurePotential_one,vectorTerminalPotential_one_time_zero]

end QuantitativePaper
