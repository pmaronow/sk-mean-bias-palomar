module
public import QuantitativePaper.VectorTailGridBound
public import QuantitativePaper.VectorDyadicLimit
public import QuantitativePaper.VectorGridCDFBound
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! A genuine arbitrary-measure vector potential at time zero, constructed
at every physical overlap as the uniform limit of concrete dyadic Gaussian
recursions. No continuous-time PDE or state/contact assertion is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

def vectorDyadicTailPotential {n : ℕ} (μ : Paper.ParisiMeasure) (β t q : ℝ) (j : ℕ)
    (p : Couplings n×ℝ) (x : Field n) : ℝ :=
  vectorTailRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t q p
    (vectorDyadicIndex j+3) x

theorem vectorDyadicTailPotential_succ_abs_sub_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1) (j : ℕ) (p : Couplings n×ℝ) (x : Field n) :
    |vectorDyadicTailPotential μ β t q (j+1) p x-vectorDyadicTailPotential μ β t q j p x| ≤
      (2*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j := by
  unfold vectorDyadicTailPotential
  rw [vectorDyadicIndex_succ]
  have hh := vectorTailRecursion_grid_adjacent_abs_sub_le μ (vectorDyadicIndex j) β t q ht hq p x
  have he : 2*vectorDyadicIndex j+1+3=2*vectorDyadicIndex j+4 := by omega
  rw [he]
  have he' : 2*(n : ℝ)*((1-t)*β^2)/(vectorDyadicIndex j+1 : ℕ)=
      (2*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j := by
    rw [vectorDyadicIndex_add_one,Nat.cast_pow,Nat.cast_ofNat,div_pow]
    ring
  exact he' ▸ hh

theorem cauchySeq_vectorDyadicTailPotential {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    CauchySeq (fun j => vectorDyadicTailPotential μ β t q j p x) := by
  apply cauchySeq_of_le_geometric (1/2) (2*(n : ℝ)*((1-t)*β^2)) (by norm_num)
  intro j
  rw [Real.dist_eq,abs_sub_comm]
  exact vectorDyadicTailPotential_succ_abs_sub_le μ β t q ht hq j p x

def vectorMeasureTailPotential {n : ℕ} (μ : Paper.ParisiMeasure) (β t q : ℝ)
    (p : Couplings n×ℝ) (x : Field n) : ℝ :=
  limUnder atTop (fun j => vectorDyadicTailPotential μ β t q j p x)

theorem tendsto_vectorDyadicTailPotential {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    Tendsto (fun j => vectorDyadicTailPotential μ β t q j p x) atTop
      (𝓝 (vectorMeasureTailPotential μ β t q p x)) :=
  (cauchySeq_vectorDyadicTailPotential μ β t q ht hq p x).tendsto_limUnder

theorem vectorDyadicTailPotential_limit_abs_sub_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1) (j : ℕ) (p : Couplings n×ℝ) (x : Field n) :
    |vectorDyadicTailPotential μ β t q j p x-vectorMeasureTailPotential μ β t q p x| ≤
      (4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j := by
  have hh := dist_le_of_le_geometric_of_tendsto (r:= (1/2 : ℝ))
    (C:=2*(n : ℝ)*((1-t)*β^2)) (by norm_num)
    (fun l => by
      rw [Real.dist_eq,abs_sub_comm]
      exact vectorDyadicTailPotential_succ_abs_sub_le μ β t q ht hq l p x)
    (tendsto_vectorDyadicTailPotential μ β t q ht hq p x) j
  rw [Real.dist_eq] at hh
  have he : (2*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j/(1-(1/2 : ℝ))=
      (4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j := by ring
  exact he ▸ hh

end QuantitativePaper
