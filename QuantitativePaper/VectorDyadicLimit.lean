module
public import QuantitativePaper.VectorDyadicRefinement
public import QuantitativePaper.VectorGridCDFBound
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! A genuine arbitrary-measure vector potential at time zero, constructed
as the uniform limit of concrete dyadic Gaussian recursions. This module does
not yet assert the continuous-time vector PDE or the state/contact identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem vectorRecursion_grid_adjacent_abs_sub_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (N : ℕ) (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (x : Field n) :
    |vectorRecursion (Paper.parisiGridRSBScheme μ (2*N+1)) β t p (2*N+4) x-
      vectorRecursion (Paper.parisiGridRSBScheme μ N) β t p (N+3) x| ≤
      2*(n : ℝ)*((1-t)*β^2)/(N+1 : ℕ) := by
  have hc : 0 ≤ (n : ℝ)*((1-t)*β^2) :=
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β))
  have hh := vectorRecursion_grid_profile_abs_sub_le μ (Paper.parisiGridMeasure μ N)
    (2*N+1) β t ht p x
  rw [vectorRecursion_grid_refine_coarse μ N β t ht p] at hh
  have he : (n : ℝ)*((1-t)*β^2)*(1/(N+1 : ℕ)+2/(2*N+1+1 : ℕ))=
      2*(n : ℝ)*((1-t)*β^2)/(N+1 : ℕ) := by
    push_cast
    field_simp
    ring
  exact hh.trans (he ▸ mul_le_mul_of_nonneg_left
    (add_le_add (Paper.parisiCDFDistance_grid_le μ N) le_rfl) hc)

def vectorDyadicIndex (j : ℕ) : ℕ := 2^j-1

theorem vectorDyadicIndex_add_one (j : ℕ) : vectorDyadicIndex j+1=2^j := by
  unfold vectorDyadicIndex
  have hh : 0<2^j := pow_pos (by omega) j
  omega

theorem vectorDyadicIndex_succ (j : ℕ) :
    vectorDyadicIndex (j+1)=2*vectorDyadicIndex j+1 := by
  have hh : 0<2^j := pow_pos (by omega) j
  simp only [vectorDyadicIndex,pow_succ]
  omega

def vectorDyadicPotential {n : ℕ} (μ : Paper.ParisiMeasure) (β t : ℝ) (j : ℕ)
    (p : Couplings n×ℝ) (x : Field n) : ℝ :=
  vectorRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t p
    (vectorDyadicIndex j+3) x

theorem vectorDyadicPotential_succ_abs_sub_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (j : ℕ) (p : Couplings n×ℝ) (x : Field n) :
    |vectorDyadicPotential μ β t (j+1) p x-vectorDyadicPotential μ β t j p x| ≤
      (2*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j := by
  unfold vectorDyadicPotential
  rw [vectorDyadicIndex_succ]
  have hh := vectorRecursion_grid_adjacent_abs_sub_le μ (vectorDyadicIndex j) β t ht p x
  have he : 2*vectorDyadicIndex j+1+3=2*vectorDyadicIndex j+4 := by omega
  rw [he]
  have he' : 2*(n : ℝ)*((1-t)*β^2)/(vectorDyadicIndex j+1 : ℕ)=
      (2*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j := by
    rw [vectorDyadicIndex_add_one,Nat.cast_pow,Nat.cast_ofNat,div_pow]
    ring
  exact he' ▸ hh

theorem cauchySeq_vectorDyadicPotential {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (x : Field n) :
    CauchySeq (fun j => vectorDyadicPotential μ β t j p x) := by
  apply cauchySeq_of_le_geometric (1/2) (2*(n : ℝ)*((1-t)*β^2)) (by norm_num)
  intro j
  rw [Real.dist_eq,abs_sub_comm]
  exact vectorDyadicPotential_succ_abs_sub_le μ β t ht j p x

def vectorMeasurePotential {n : ℕ} (μ : Paper.ParisiMeasure) (β t : ℝ)
    (p : Couplings n×ℝ) (x : Field n) : ℝ :=
  limUnder atTop (fun j => vectorDyadicPotential μ β t j p x)

theorem tendsto_vectorDyadicPotential {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (x : Field n) :
    Tendsto (fun j => vectorDyadicPotential μ β t j p x) atTop
      (𝓝 (vectorMeasurePotential μ β t p x)) :=
  (cauchySeq_vectorDyadicPotential μ β t ht p x).tendsto_limUnder

theorem vectorDyadicPotential_limit_abs_sub_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (j : ℕ) (p : Couplings n×ℝ) (x : Field n) :
    |vectorDyadicPotential μ β t j p x-vectorMeasurePotential μ β t p x| ≤
      (4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j := by
  have hh := dist_le_of_le_geometric_of_tendsto (r:= (1/2 : ℝ))
    (C:=2*(n : ℝ)*((1-t)*β^2)) (by norm_num)
    (fun l => by
      rw [Real.dist_eq,abs_sub_comm]
      exact vectorDyadicPotential_succ_abs_sub_le μ β t ht l p x)
    (tendsto_vectorDyadicPotential μ β t ht p x) j
  rw [Real.dist_eq] at hh
  have he : (2*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j/(1-(1/2 : ℝ))=
      (4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j := by ring
  exact he ▸ hh

end QuantitativePaper
